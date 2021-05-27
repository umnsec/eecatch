#include <llvm/Pass.h>
#include <llvm/IR/DebugInfo.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Value.h>
#include <llvm/IR/CFG.h>
#include <llvm/IR/InlineAsm.h>

#include "ExaggerateError.h"
#include "Config.h"
#include "Common.h"
#include "regex"
#include "algorithm"

using namespace llvm;
using namespace std;

//#define DEBUG_PRINT true
//#define TEST_CASE true
//#define INTRA_PROC true
#define PRINT_RESULT true
#define DEFAULT_HANDLE true
#define INIT_EXIT_PAIRS true
//#define SEVERE_ERR true 

// Refine the assembly functions to detect more SecurityChecks
static const std::regex print_pattern("[a-z0-9A-Z_]+(\\s*)(?=\\(*)");
static const std::regex func_pattern("[a-z0-9A-Z_]+(\\s*)(?=\\()");
static const std::regex alloc_func( 
	"(?:(?:devm_)?(?:kv|k|v)[czm]alloc(?:_node|_array)?|"
	"kstrdup(?:_const)?|kmemdup(?:_nul)?)|"
	"(?:\\w+)?alloc_skb(?:ip_align)?|dma_alloc_coherent");

// static members initialization
std::list<ErrorFactors> ExaggerateErrPass::EFList;
std::set<StringRef> ExaggerateErrPass::InitFuncSet;
std::set<StringRef> ExaggerateErrPass::ExitFuncSet;
std::map<SecurityCheck *, HandleList> ExaggerateErrPass::ScHandleMap;
std::map<Function *, std::set<Value *>> ExaggerateErrPass::FnRvalMap;
std::map<CallInst *, SecurityCheck *> ExaggerateErrPass::CallerSCkMap;
std::map<struct ErrorRecord, HListMaxPair> ExaggerateErrPass::ErrorCountMap;
std::set<std::pair<SecurityCheck *, unsigned>> ExaggerateErrPass::ResultSet;

// constants
const std::set<unsigned> MustErrFlags = {1,16};
const std::set<unsigned> LogErrFlags = {17,18};

const float threshold = 0.7;
const unsigned severeErrLevel = WARNING;

//
//
// Exaggerated Error Handling implementation
//
// For each function, collect all the return error values returned
// Map the security check to the CallInst, if any
// Collect set of Init and Exit function sets.
bool ExaggerateErrPass::doInitialization(Module *M) {

	std::set<GlobalVariable *> GVSet;
	for (auto &GV : M->globals())
		if (GV.getSection().find("discard.addressable") != std::string::npos)
			GVSet.insert(&GV);

	for (Function &f : *M) {
		LPSet.clear();
		Function *F =  &f;

		if (F->empty())
			continue;

		// Data Structure 0: Collect all Init & Exit Functions
		checkFuncSection(F);

		if (Ctx->UnifiedFuncSet.find(F) == Ctx->UnifiedFuncSet.end()) 
			continue;

		// Data Structure 1: Map each Function * to set of ErrVal it returns
		std::set<Value *> ErrValSet;
		std::set<Function *> VisitedFnSet;
		if (FnRvalMap.find(F) == FnRvalMap.end()) {
			collectReturnValues(F, ErrValSet, VisitedFnSet);
			FnRvalMap[F] = ErrValSet;
		}

		set<SecurityCheck> SCSet = Ctx->SecurityCheckSets[F];
		if (SCSet.empty())
			continue;

		// Data Structure 2: Map each SC if it is a CallInst src fn
		for (auto SCheck : SCSet) {
			set<Value *> CTSet;
			Value *SC = SCheck.getSCheck();

			identifyTargets(SC, CTSet);
			for (auto CT : CTSet) {
				CallInst *CI = dyn_cast<CallInst>(CT);
				if (!CI) continue;

				// Return value as source: Collect called functions 
				CallSite CS(CI);
				Function *CF = CI->getCalledFunction();
				bool setAsm = false;

				if (!CF) {
					// Check if CI is an Assembly function
					string line;
					getSourceCodeLine(CI, line);

					for (string s : ErrAsmVector)
						if (line.find(s) != std::string::npos) {
							if (CallerSCkMap.find(CI) == CallerSCkMap.end())
								CallerSCkMap[CI] = &SCheck;

							setAsm = true;
							break;
						}
				}

				if (setAsm) continue;

				if (Ctx->Callees[CI].size())
					CF = *(Ctx->Callees[CI].begin());
				if (!CF)
					continue;

				if (CallerSCkMap.find(CI) == CallerSCkMap.end())
					CallerSCkMap[CI] = &SCheck;
			}
		}
	}

  return false;
}

bool ExaggerateErrPass::doFinalization(Module *M) {

	if (Ctx->Modules.size() == MIdx) {
		OP << ExitFuncSet.size() << " Exit Func Size\n"
		 << InitFuncSet.size() << " Init Func Size\n";
	}
	++MIdx;

#ifdef DEBUG_PRINT
	for (Function &f : *M) {
		Function *F =  &f;

		if (FnRvalMap.find(F) != FnRvalMap.end()) {
			std::set<Value *> ErrValSet = FnRvalMap[F];
			OP << "\n" << F->getName() << " size " << ErrValSet.size() << "\n";
			for (auto V : ErrValSet)
				OP << *V << "\n";
		}
	}
#endif
  return false;
}

// Starting point for the Pass
bool ExaggerateErrPass::doModulePass(Module *M) {

	++MIdx;
	string dir;
	getSpatialCtx(M->getModuleIdentifier(), dir);

	for(Function &F : *M) {

#if defined(DEBUG_PRINT) && defined(TEST_CASE)
		// Only test the specified functions
		if (F.getName() != "dccp_ackvec_lookup")
			continue;
#endif

		if (F.empty())
			continue;

		if (Ctx->UnifiedFuncSet.find(&F) == Ctx->UnifiedFuncSet.end()) 
			continue;

#ifdef INTRA_PROC
		if (!F.getReturnType()->isVoidTy()) 
			continue;
#endif

		// First step collect errors, their context, and the handling
		CallSeverityMap.clear();
		set<SecurityCheck *> SCSet;
		SecurityChecksPass::EdgeErrMap EEMap;
		SCP.identifySecurityChecks(&F, EEMap, SCSet);

		if (SCSet.empty())
			continue;

#ifdef DEBUG_PRINT
		OP<<"Working on function: \033[32m" << F.getName() 
			<< " with " << SCSet.size() << " SChecks\033[0m\n";
#endif

		// Determine the type of function (regular, init, exit)
		unsigned temporalCtx = getTemporalCtx(F);

		// Collect sources, spatial, and temporal Ctx, error handling per SCheck
		for (auto SC : SCSet) {
			HandleList HList;
			ErrorFactors EF(SC);

			EF.setSpatialCtx(dir);
			EF.setTemporalCtx(temporalCtx);

			// TODO(APK): Execute else branch once copy_from_user test is done
#if 0
			std::set<err_t> &err_set = EF.getErrorSet();
			bool foundErr = copyErrors(&F, SC, err_set);
#else
			bool foundErr = determineErrors(&F, SC, EF);
#endif

#ifdef DEBUG_PRINT
			std::set<err_t> &err_set = EF.getErrorSet();
			if (err_set.empty()) 
				printSourceCodeInfo(SC->getSCheck());
#endif
			
			if (!foundErr)
				continue;

			ExtractErrorSeverity(&F, SC, EEMap, HList);
			ScHandleMap[SC] = HList;

			EFList.push_back(EF);
			updateErrorCounts(&EF);

#ifdef DEBUG_PRINT
			if (!HList.empty()) {
				OP << "Security Check:";
				printSourceCodeInfo(SC->getSCheck());

				std::set<err_t> &err_set = EF.getErrorSet();
				OP << "Errors:\t";
				for (auto &et : err_set) {
					OP << et.first << " and IR: ";
					if (Function *EF = dyn_cast<Function>(et.second))
						OP << EF->getName() << " :Fn\n";
					else
						OP << *et.second << "\n";
				}

				OP << "\nHandling level: ";
				for (auto &x : HList) {
					OP << (unsigned)x.first << " by "; 
					printSourceCodeInfo(x.second);
				}
				OP << "============================\n";
			}
#endif
		}
		// continue;

#ifdef DEBUG_PRINT
		OP << "Post " << F.getName() << " ECMap has " << 
				ErrorCountMap.size() << " errors\n";
#endif
	} // End of function iteration 

	if (Ctx->Modules.size() == MIdx) {
		removeUninterstingRecords();

#ifdef DEBUG_PRINT
		for (auto pair : ErrorCountMap) {
			ErrorRecord ER = (pair.first);
			HListMaxPair &SMP = (pair.second);
			for (auto &x : SMP.first)
				OP << (unsigned)x.first << ", ";
			OP << "\tCtx: " << ER.spatialCtx << " ";
			OP << ER.temporalCtx << " ";
			OP << SMP.second << "\n";
			//OP << "Error: " << *ER.Error << "\n";
		}
#endif

		// Perform analysis at the end of processing all modules
		OP << "Performing Statistical analysis on the results"
					" from phase 1\n\n";
		performStatisticalAnalysis();
		OP << "Detected " << ResultSet.size() << " exaggerated errors \n";
	}

  return false;
}

// Collect all the init functions and their callers
void ExaggerateErrPass::checkFuncSection(Function *F) {

	if (!F->hasSection())
		return;

	if (Ctx->UnifiedFuncSet.find(F) == Ctx->UnifiedFuncSet.end())
		return;

	checkFunctionExit(F);

	if (F->getSection().find("init") == std::string::npos)
		return;

	std::list<Function *> FnList;
	FnList.push_back(F);
	while (!FnList.empty()) {

		Function *IF = FnList.front();
		StringRef FName = IF->getName();
		FnList.pop_front();

		if (InitFuncSet.find(FName) != InitFuncSet.end())
			continue;
		InitFuncSet.insert(FName);

		for (auto CI : Ctx->Callers[IF]) {
			Function *CF = CI->getCalledFunction();
			if (!CF)
				continue;	
			FnList.push_back(CF);
		}
	}
}

void ExaggerateErrPass::checkFunctionExit(Function *F) {

	if (F->getSection().find("exit") == std::string::npos) 
		return;

	std::list<Function *> FnList;
	FnList.push_back(F);
	while (!FnList.empty()) {

		Function *IF = FnList.front();
		StringRef FName = IF->getName();
		FnList.pop_front();

		if (FName.find("llvm") != std::string::npos || FName.empty())
			continue;
		if (ExitFuncSet.find(FName) != ExitFuncSet.end())
			continue;
		ExitFuncSet.insert(FName);

		if (IF->empty())
			continue;

		// Iterate over the instructions and collect callees
		inst_iterator i = inst_begin(IF), e = inst_end(IF);
		for (; i != e; ++i) {
			CallInst *CI = dyn_cast<CallInst>(&*i);
			if (!CI)
				continue;
			Function *CF = CI->getCalledFunction();

			if (!CF) continue;

			if (Ctx->Callees[CI].size())
				CF = *(Ctx->Callees[CI].begin());
			if (!CF) 
				continue;

			FnList.push_back(CF);
		}
	}
}

// Extract all possible errors returned from a function
void ExaggerateErrPass::collectReturnValues(Function *F, 
					std::set<Value *> &EVSet,
					std::set<Function *>& VisitedFnSet) {
	std::set<Value *> Visited;
	string FuncName = static_cast<std::string>(F->getName());

	//void return function 
	if (F->getReturnType()->isVoidTy())
		return;

	// Functions stored to avoid loops
	if (VisitedFnSet.find(F) != VisitedFnSet.end()) {
		EVSet.insert(FnRvalMap[F].begin(), FnRvalMap[F].end());
		return;
	}
	VisitedFnSet.insert(F);

	for (inst_iterator i = inst_begin(F), e = inst_end(F);
			i != e; ++i) {
		// Backward search from RetInst
		if (ReturnInst *RI = dyn_cast<ReturnInst>(&*i)) 
			performEEBackwardAnalysis(F, RI->getReturnValue(), EVSet, Visited);
	}

	if (EVSet.empty())
		return;

	std::set<Value *> TmpSet;
	for (auto V : EVSet) {
		if (CallInst *CI = dyn_cast<CallInst>(V))
			TmpSet.insert(V); 
	}

	if (TmpSet.empty())
		return;

	// If the return value of a CallInst is marked as returning an error
	// replace the callInst with the return values from the Caller
	for (auto V : TmpSet) {
		CallInst *CI = dyn_cast<CallInst>(V);
		Function *CF = CI->getCalledFunction();

		// TODO(APK): Store the errors from Indirect calls and InlineAsm ?
		if (!CF) continue;

		if (Ctx->Callees[CI].size())
			CF = *(Ctx->Callees[CI].begin());
		if (!CF) 
			continue;

		std::set<Value *> RecurseEVSet;
		if (FnRvalMap.find(CF) != FnRvalMap.end()) {
			RecurseEVSet.insert(FnRvalMap[CF].begin(), FnRvalMap[CF].end());
		} else {
			collectReturnValues(CF, RecurseEVSet, VisitedFnSet);
			FnRvalMap[CF] = RecurseEVSet;
		}

		EVSet.erase(V);
		EVSet.insert(RecurseEVSet.begin(), RecurseEVSet.end());

	}
}

bool ExaggerateErrPass::determineErrors(Function *F, SecurityCheck *SC, 
					ErrorFactors &ErrF) {

	Value *Check = SC->getSCheck();
	Value *Branch = SC->getSCBranch();
	set<err_t> &ErrorSet = ErrF.getErrorSet();

	if (Instruction *SCI = dyn_cast<Instruction>(Check)) {
		bool foundErr = backtrackSource(F, SCI, ErrorSet);
		
		// Second level of error checking - predicate value
		foundErr |= evaluatePredicate(F, SCI, &ErrorSet);
		return foundErr;
	}

	// SCheck is empty, find error based on the SCBranch
	std::set<Value *> ArgSet;
	for (auto I = F->arg_begin(), E = F->arg_end(); I != E; ++I)
		ArgSet.insert(dyn_cast<Value>(&*I));

	if (ArgSet.find(Check) != ArgSet.end()) {
		err_t Err = std::make_pair(DEFLTVAL, Check);
		ErrorSet.insert(Err);
		return true;
	}

	if (SwitchInst *SwI = dyn_cast<SwitchInst>(Branch)) {
		Value *V = SwI->getCondition();
		if (ArgSet.find(V) != ArgSet.end()) {
			err_t Err = std::make_pair(DEFLTVAL, V);
			ErrorSet.insert(Err);
			return true;
		}
		assert(false && "SwitchInst with no param");
	}

	if (BranchInst *BI = dyn_cast<BranchInst>(Branch)) {
		Value *V = BI->getCondition();
		if (ArgSet.find(V) != ArgSet.end()) {
			err_t Err = std::make_pair(DEFLTVAL, V);
			ErrorSet.insert(Err);
			return true;
		}
	}

	if (SelectInst *SeI = dyn_cast<SelectInst>(Branch)) {
		Value *TV = SeI->getTrueValue();
		Value *FV = SeI->getFalseValue();
		Value *V = nullptr;
		if (ArgSet.find(TV) != ArgSet.end())
			V = TV;
		if (ArgSet.find(FV) != ArgSet.end())
			V = FV;

		if (!V)
			return false;

		err_t Err = std::make_pair(DEFLTVAL, V);
		ErrorSet.insert(Err);
		return true;
	}

#ifdef DEBUG_PRINT
	OP << *SC->getSCBranch() << " in " << F->getName() 
			<< " not captured\n";
#endif

	return false;
}

// This is a validation attempt to ensure that, we are indeed 
// capturing the error found in the predicate
bool ExaggerateErrPass::evaluatePredicate (Function *F, 
				Instruction *SCI, set<err_t> *ErrorSet) {
	
	ICmpInst *CmpI = dyn_cast<ICmpInst>(SCI);
	if (!CmpI)
		return false;

	ICmpInst::Predicate Pred = CmpI->getPredicate();
	Value *V = CmpI->getOperand(1);
	if (!isa<Constant>(V)) 
		return false;

	if (Pred == ICmpInst::ICMP_EQ || Pred == ICmpInst::ICMP_NE) {
		if (isa<ConstantPointerNull>(V)) {
			err_t Err = std::make_pair(NULLVAL, V);
			ErrorSet->insert(Err);
			return true;
		}

		if (!SCP.isValueErrno(V, F)) {
			// Non error cases ?
			return false;
		}

		if (ConstantInt *CI = dyn_cast<ConstantInt>(V)) {
			err_t Err = std::make_pair(CI->getValue().getSExtValue(), V);
			ErrorSet->insert(Err);
			return true;
		}

#if 0
		if (ConstantExpr *CE = dyn_cast<ConstantExpr>(V)) {
			for (unsigned i = 0, e = CE->getNumOperands(); i != e; ++i) 
				if (SCP.isValueErrno(CE->getOperand(i), F)) {
					err_t Err = std::make_pair(static_cast<int>(
						CE->getOperand(i)->getUniqueInteger().getSExtValue()), V);
					ErrorSet->insert(Err);
					return true;
				}
		}
#endif
	}

	return false;
}

// Determine the source by determining the critical variable
bool ExaggerateErrPass::backtrackSource(Function *F, Instruction *SCI,
					set<err_t> &ErrSet) {

	set<Value *> CTSet;
	identifyTargets(SCI, CTSet);

	if (CTSet.empty())
		return false;

	set<BasicBlock *> predBBs;
	DFA.collectPredReachBlocks(SCI->getParent(), predBBs);

	// Collect sources for 3 types of categories, arguments, retval & param
	for (auto CT : CTSet) {
		int8_t ArgNo = -1;

		// 1. Argument as source: Collect indirect calls of argument sources
		if (Argument *Arg = dyn_cast<Argument>(CT)) {

			if (!F->hasAddressTaken())
				continue;

			for (Function::arg_iterator ai = F->arg_begin(),
					ae = F->arg_end(); ai != ae; ++ai) {
				++ArgNo;
				if (Arg == &*ai)
					break;
			}

			for (auto CI : Ctx->Callers[F]) {
				// Indirect call
				if (CI->getCalledFunction() != NULL) {
					continue;	
				}
				// Collect indirect calls and argument number as source
				err_t Err = std::make_pair(DEFLTVAL, CI);
				ErrSet.insert(Err);
			}

		} else if (CallInst *CI = dyn_cast<CallInst>(CT)) {
			// 2. return value of direct calls
			collectErrorCallInst(CI, ErrSet);
		
		} else if (isa<Constant>(CT)) {
			// 3. Constants that can be error values
			collectErrorConstants(F, CT, ErrSet);
		
		} else {
		// 4. Parameter as source: Also collect called functions in direct calls
			for (User *U : CT->users()) {
				CallInst *CI = dyn_cast<CallInst>(U);
				if (!CI)
					continue;
				if (predBBs.find(CI->getParent()) != predBBs.end()) {
					int8_t ArgNo = -1;
					CallSite CS(CI);
					for (CallSite::arg_iterator ai = CS.arg_begin(),
							ae = CS.arg_end(); ai != ae; ++ai) {
						++ArgNo;
						if (CT == *ai)
							break;
					}
					if (ArgNo == -1)
						continue;

					Function *CF = CI->getCalledFunction();
					if (!CF) continue;

					if (Ctx->Callees[CI].size())
						CF = *(Ctx->Callees[CI].begin());
					if (!CF) continue;

					err_t Err = std::make_pair(DEFLTVAL, CF);
					ErrSet.insert(Err);
				}
			}
		}
	} // Finish iterating the CTSet
	return true;
}

// Return value as source: Collect called functions
void ExaggerateErrPass::collectErrorCallInst(CallInst *CI,
												set<err_t> &ErrSet) {
	smatch match;
	Function *CF = CI->getCalledFunction();
	CallSite CS(CI);
	bool setIndirect = false, setAsm = false;

	if (CS.isIndirectCall()) {
		setIndirect = true;
	} else if (!CF) {
		string line;
		getSourceCodeLine(CI, line);

		for (string s : ErrAsmVector)
			if (line.find(s) != std::string::npos) {
				err_t Err = std::make_pair(DEFLTVAL, CI);
				ErrSet.insert(Err);
				setAsm = true;
				break;
			}

#if DEBUG_PRINT
		if (!setAsm) 
			OP << "Failed to capture " << line << "\n";
#endif
		return;
	}

	// Errors are allocation functions
	if (!setIndirect) {
		std::string FnName = static_cast<std::string>(CF->getName());
		if (regex_search(FnName, match, alloc_func)) {
			Type *i32_type = IntegerType::getInt32Ty(CF->getContext());
			Value *V = llvm::ConstantInt::get(i32_type, ALLOCVAL);
			err_t Err = std::make_pair(ALLOCVAL, V);
			ErrSet.insert(Err);
			return;
		}
	}

	// Direct calls only store the first callee info
	FuncSet& FS = Ctx->Callees[CI];
	if (FS.empty())
		return;

	if (!setIndirect) {
		CF = *FS.begin();
		FS.clear();
		FS.insert(CF);
	}

	// Granularity of the error is the return value of the Caller instead
	// of the function name for those with returning error values. 
	for (Function *Callee : FS) {
		if (!Callee) 
			continue;

		if (FnRvalMap.find(Callee) != FnRvalMap.end()) {
			std::set<Value *> FnErrSet = FnRvalMap[CF];
			//OP << *CI << " " << Callee->getName() << " " << ErrorSet.size() << "\n";
			for (auto E : FnErrSet) {
				err_t Err = std::make_pair(DEFLTVAL, CF);
				ErrSet.insert(Err);
			}
		}
	}
}

void ExaggerateErrPass::collectErrorConstants(Function *F, Value *V, 
					set<err_t> &ErrorSet) {

	if (isa<ConstantPointerNull>(V)) {
		err_t Err = std::make_pair(NULLVAL, V);
		ErrorSet.insert(Err);
		return;
	}

	if (!SCP.isValueErrno(V, F)) {
		// Non error cases ?
		return;
	}

	if (ConstantInt *CI = dyn_cast<ConstantInt>(V)) {
		err_t Err = std::make_pair(CI->getValue().getSExtValue(), V);
		ErrorSet.insert(Err);
		return;
	}

#if 0
	if (ConstantExpr *CE = dyn_cast<ConstantExpr>(V)) {
		for (unsigned i = 0, e = CE->getNumOperands(); i != e; ++i) 
			if (SCP.isValueErrno(CE->getOperand(i), F)) {
				err_t Err = std::make_pair(static_cast<int>(
						CE->getOperand(i)->getUniqueInteger().getSExtValue()), V);
				ErrorSet.insert(Err);
				return;
			}
	}
#endif
}

// Extract the CV from a SecurityCheck
// Same as identifyCheckedTargets from MissingChecks.cc
void ExaggerateErrPass::identifyTargets(Value *V, set<Value *> &CTSet) {

	set<Value *> TrackedSet;
	set<Value *> CVSet;
	Value *SCOpd;

	if (ICmpInst *ICmp = dyn_cast<ICmpInst>(V)) {
		for (unsigned i = 0, ie = ICmp->getNumOperands(); i < ie; i++) {
			SCOpd = ICmp->getOperand(i);
			DFA.findInFuncSourceCV(SCOpd, CTSet, CVSet, TrackedSet);
		}

	} else if (FCmpInst *FCmp = dyn_cast<FCmpInst>(V)) {
		for (unsigned i = 0, ie = FCmp->getNumOperands(); i < ie; i++) {
			SCOpd = FCmp->getOperand(i);
			DFA.findInFuncSourceCV(SCOpd, CTSet, CVSet, TrackedSet);
		}

	} else if (BinaryOperator *BO = dyn_cast<BinaryOperator>(V)) {
		for (unsigned i = 0, ie = BO->getNumOperands(); i < ie; i++) {
			SCOpd = BO->getOperand(i);
			DFA.findInFuncSourceCV(SCOpd, CTSet, CVSet, TrackedSet);
		}

	} else if (UnaryInstruction *UI = dyn_cast<UnaryInstruction>(V)) {
		SCOpd = UI->getOperand(0);
		DFA.findInFuncSourceCV(SCOpd, CTSet, CVSet, TrackedSet);

	} else if (PHINode *PN = dyn_cast<PHINode>(V)) {
		for (unsigned i = 0, e = PN->getNumIncomingValues(); i != e; ++i) {
			SCOpd = PN->getIncomingValue(i);
			DFA.findInFuncSourceCV(SCOpd, CTSet, CVSet, TrackedSet);
		}

	} else if (CallInst *CI = dyn_cast<CallInst>(V)) {
		auto AI = CI->arg_begin(), E = CI->arg_end(); 
		// No arguments, use the function as the source
		if (AI == E) {
			CTSet.insert(CI);
			return;
		}

		for (; AI != E; ++AI) {
			Value* Param = dyn_cast<Value>(&*AI);
			DFA.findInFuncSourceCV(Param, CTSet, CVSet, TrackedSet);
		}

	} else if (SelectInst *SI = dyn_cast<SelectInst>(V)) {
		DFA.findInFuncSourceCV(SI->getTrueValue(), CTSet, CVSet, TrackedSet);
		DFA.findInFuncSourceCV(SI->getFalseValue(), CTSet, CVSet, TrackedSet);
	}

	return;
}

unsigned ExaggerateErrPass::getTemporalCtx(Function &F) {

	unsigned temporalCtx = REGULAR;
	if (F.hasSection()) {
		StringRef section = F.getSection();
		if (section.find("init") != std::string::npos)
			temporalCtx = INIT;
		else if (section.find("exit") != std::string::npos)
			temporalCtx = EXIT;
		else 
			temporalCtx = INIT;
			// __sched, __ref are macros that are hard to justify as regular functions
			//OP << F.getName() << " " << section << " Failed \n"; 
			//assert(false && "Caught a section not identified earlier");
	}

	return temporalCtx;
}

bool ExaggerateErrPass::getSpatialCtx(const string &s, string &dir) {

	auto it = s.find("bc-5.3.0/");
	if (it != std::string::npos) {
		it = it+9;
		auto end = s.find("/", it);
		dir = s.substr(it, end-(it));

		// If in net, fs, or drivers, perform second level refinement
		if (RefinedSet.find(dir) != RefinedSet.end()) {
			it = it + dir.length() + 1;
			end = s.find("/", it);
			if (end != std::string::npos)
				dir = dir + "/" + s.substr(it, end-(it));
		}
	}

	return false;
}

// Determine the level the error is handled in the error path
void ExaggerateErrPass::ExtractErrorSeverity(Function *F, SecurityCheck *SC,
					SecurityChecksPass::EdgeErrMap &EEMap, HandleList &HList) {

	bool isReturned = false;
	std::set<Value *> Visited;
	uint8_t severity = DEFAULT; 

	Value *Check = SC->getSCheck();
	Value *Branch = SC->getSCBranch();
	std::set<Function *> CoveredFuncSet;

	assert((isa<SwitchInst>(Branch) || isa<BranchInst>(Branch) ||
				isa<SelectInst>(Branch)) && "Unknow Inst type");

#ifdef DEBUG_PRINT
	OP << "Check: " << *Check <<  "\nBranch: " << *Branch << "\n";
	printSourceCodeInfo(Check);
#endif

	// 1. All SelectInst Branches return error back to the Caller
	if (SelectInst *SeI = dyn_cast<SelectInst>(Branch)) {
		Value *TV = SeI->getTrueValue();
		Value *FV = SeI->getFalseValue();

		bool flag1 = SCP.isValueErrno(TV, F);
		bool flag2 = SCP.isValueErrno(FV, F);
		assert(((flag1 && !flag2) || (!flag1 && flag2)) && "Incorrect state");

		determineErrorReturn(SeI, Visited, &isReturned);

		assert(isReturned && "Failed case"); 

		forwardInterErrHandling(F, SeI, CoveredFuncSet, HList);
		return;
	}

	// 2. BranchInst or SwitchInst returns error back to caller
	unsigned edgeFlag = 0;
	determineErrorBlock(SC, EEMap, edgeFlag);

	BasicBlock *Head = dyn_cast<Instruction>(Branch)->getParent();
	Instruction *TI = Head->getTerminator();

	for (unsigned i = 0, e = Head->getTerminator()->getNumSuccessors();
			i != e; ++i) {
		BasicBlock *BB = Head->getTerminator()->getSuccessor(i);
		if (!BB) continue;

		SecurityChecksPass::CFGEdge Edge = std::make_pair(TI, BB);
		if (EEMap.count(Edge) && EEMap[Edge] != edgeFlag) 
			continue;

		for (auto &Inst : *BB) {
			PHINode *PN = dyn_cast<PHINode>(&Inst);
			if (!PN) 
				continue;
			for (unsigned I = 0, E = PN->getNumIncomingValues(); I != E; ++I) {
				if (PN->getIncomingBlock(I) != Head) 
					continue;
				determineErrorReturn(PN, Visited, &isReturned);

				if (isReturned) {
					forwardInterErrHandling(F, Check, CoveredFuncSet, HList);
					return;
				}
			}
		} // Iterate over the Instructions in BB

		// 3. General case, collect the successors of the BasicBlock
		BBPath Path;
		std::set<BBPath> PathSet;
		std::set<BasicBlock *> visitedBB;

		DFS(BB, Path, visitedBB, PathSet, EEMap, edgeFlag);
#ifdef DEBUG_PRINT
		OP << "Evaluating path with flag: " << edgeFlag << " having " 
			<< PathSet.size() << " BB(s)\n";
#endif

		Value *V;
		visitedBB.clear();
		isReturned = false;
		HandlePair hpair = std::make_pair(DEFAULT, V);

		for (BBPath BP : PathSet) {
			searchLoggingFn(BP, isReturned, visitedBB, hpair);
			isReturned |= isReturned;
		}

		if (hpair.first != DEFAULT) {
			HList.push_back(hpair);
			return;
		}

		if (isReturned) {
			forwardInterErrHandling(F, Check, CoveredFuncSet, HList);
			return;
		}

		if (hpair.first == DEFAULT && !isReturned) 
			OP << "Investigate " << *Check << " in " << F->getName() << "\n";

	} //End of successor iteration

	// If function returns void, SC is handled within the same func
	bool isVoidRet = F->getReturnType()->isVoidTy();
	if (!isReturned && isVoidRet) 
		OP << "Error case " << *Check << " in " << F->getName() << "\n";
	
	return;
}

// Given the SC in the current function returns error rather handling, 
// we backtrack until we determine where the error is handled
void ExaggerateErrPass::forwardInterErrHandling(Function *F, Value *V, 
						std::set<Function*> &CFSet, HandleList &HList) {

	SecurityCheck *SC = nullptr;
	if (Ctx->Callers.find(F) == Ctx->Callers.end())
		return;

	if (CFSet.find(F) != CFSet.end())
		return;
	CFSet.insert(F);

	// For each caller, determine severity
	for (auto CI : Ctx->Callers[F]) {

		// Caller is a Security Check
		if (CallerSCkMap.find(CI) != CallerSCkMap.end()) {
			SC = CallerSCkMap[CI];

			// SecurityCheck is already processed
			if (ScHandleMap.find(SC) != ScHandleMap.end()) {
				HandleList THList = ScHandleMap[SC];
				for (auto &x : THList)
					HList.push_back(x);

				return;
			}
		}

		// Caller is not a security check (OR)
		// Security check is not processed yet
		HandleList RFList;
		bool isReturned = false;
		std::set<Value *> Visited;

		Function *CF = CI->getParent()->getParent();
		if (!CF) continue;

		determineErrorReturn(CI, Visited, &isReturned);

		// Recurse since the callers are passing it to their callers
		if (isReturned) 
			forwardInterErrHandling(CF, V, CFSet, RFList);
#ifndef DEFAULT_HANDLE
		// WARNING is the default level of error handling in Kernel
		else
			HList.push_back(std::make_pair(WARNING, V));
#endif
		
		if (SC) {
			ScHandleMap[SC] = RFList;
		} else {
			for (auto &h : RFList)
				HList.push_back(h);
		}
	}
}

// Determine how the error from Branch is handled in the function
void ExaggerateErrPass::determineErrorReturn (Value *Target, 
					std::set<Value *> &Visited, bool* isReturned) {

	if (!Target) return;

	if (*isReturned) return;

	if (Visited.find(Target) != Visited.end()) 
		return;
	Visited.insert(Target);

	//OP << "T: " << *Target << "\n";
	for (User *U : Target->users()) {

		Instruction *I = dyn_cast<Instruction>(U);
		if (!I) continue;

		// Expect all SelectInst to reach this point
		ReturnInst *RI = dyn_cast<ReturnInst>(U);
		if (RI && RI->getReturnValue() == Target) {
			*isReturned = true;
			return;
		}

		if (SelectInst *SeI = dyn_cast<SelectInst>(U)) {
			if (Target == SeI->getTrueValue() || Target == SeI->getFalseValue())
				determineErrorReturn(U, Visited, isReturned);
		}

		// If SCBranch is a BranchInst
		if (PHINode *PN = dyn_cast<PHINode>(U)) {
			for (unsigned i = 0, e = PN->getNumIncomingValues(); i != e; ++i) {
				if (PN->getIncomingValue(i) == Target) 
					determineErrorReturn(PN, Visited, isReturned);
			}

			continue;
		}

		if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(U)) {
			if (GEP->getPointerOperand() == Target)
				determineErrorReturn(U, Visited, isReturned);

			continue;
		}

		// StoreInst is fine as ValueOperand, check the loads
		if (StoreInst *SI = dyn_cast<StoreInst>(U)) {
			if (SI->getValueOperand() == Target) {

				// get Alias of the StoredValue
				BasicBlock *BorderBB = dyn_cast<Instruction>(U)->getParent();
				set<BasicBlock *> reachBB;
				DFA.collectSuccReachBlocks(BorderBB, reachBB);

				set<Value *> AliasSet;
				DFA.getAliasPointers(SI->getPointerOperand(), AliasSet, 
						Ctx->FuncPAResults[SI->getParent()->getParent()]);
				for (Value *A : AliasSet) {
					for (User *AU : A->users()) {

						Instruction *I = dyn_cast<Instruction>(AU);
						if (!I) continue;

						if (I->getParent() != BorderBB && 
								reachBB.find(I->getParent()) == reachBB.end())
							continue;

						if (LoadInst *LI = dyn_cast<LoadInst>(AU)) 
							determineErrorReturn(AU, Visited, isReturned);
					}
				}// End Alias Set
			}

			continue;
		}

		BinaryOperator *BO = dyn_cast<BinaryOperator>(U);
		if (BO) {
			for (unsigned i = 0, e = BO->getNumOperands(); i != e; ++i) {
				Value *Opd = BO->getOperand(i);
				if (isConstant(Opd))
					continue;

				determineErrorReturn(BO, Visited, isReturned);
			}
		}

		if (UnaryInstruction *UI = dyn_cast<UnaryInstruction>(U)) {
			Value *UO = UI->getOperand(0);
			if (UO == Target)
				determineErrorReturn(UI, Visited, isReturned);
			continue;
		}

		if (ICmpInst *IC = dyn_cast<ICmpInst>(U)) {
			if (IC->getOperand(0) == Target)
				determineErrorReturn(U, Visited, isReturned);
			continue;
		}

		// Handle BranchInst for interprocedural analysis
		if (BranchInst *BI = dyn_cast<BranchInst>(U)) {
			BasicBlock *TBB = BI->getParent();
			if (BI->getCondition() != Target) 
				continue;

			for (unsigned bi = 0 ,be = BI->getNumSuccessors(); bi != be; ++bi) {
				BasicBlock *BB = BI->getSuccessor(bi);
				for (Instruction &I : *BB) {
					PHINode *PN = dyn_cast<PHINode>(&I);
					if (!PN) continue;

					for (unsigned pi = 0, pe = PN->getNumIncomingValues(); 
							pi != pe; ++pi) {
						if (PN->getIncomingBlock(pi) != TBB) 
							continue;

						Visited.insert(BI);
						determineErrorReturn(PN, Visited, isReturned);
					}
				} // End of Instruction iteration
			} // End of successor search

			continue;
		}

	} // Finish the users
}

void ExaggerateErrPass::determineErrorBlock(SecurityCheck *SC, 
				SecurityChecksPass::EdgeErrMap &EEMap, 
				unsigned &edgeFlag) {
	Value *Check = SC->getSCheck();
	Value *Branch = SC->getSCBranch();

	assert((isa<BranchInst>(Branch) || isa<SelectInst>(Branch) ||
		isa<SwitchInst>(Branch)) && "Unknown Branch Instruction");

	BasicBlock *Head = dyn_cast<Instruction>(Branch)->getParent();
	Instruction *TI = Head->getTerminator();
	unsigned succ = TI->getNumSuccessors();

	std::set<SecurityChecksPass::CFGEdge> EdgeSet;
	for (unsigned i = 0; i < succ; ++i) {
		BasicBlock *BB = TI->getSuccessor(i);
		if (!BB) continue;

		SecurityChecksPass::CFGEdge Edge = std::make_pair(TI, BB);
		if (EEMap.count(Edge)) 
			EdgeSet.insert(Edge);
	}

	// SelectInst with return in same BasicBlock
	if (!succ) return;

	// Unconditional Branch from SelectInst
	if (succ == 1) {
		auto it = EdgeSet.begin();
		edgeFlag = EEMap[*it];
		return;
	}

	Head = nullptr;
	// Must handle/Return error BasicBlock
	for (auto edge : EdgeSet) 
		if (EEMap[edge] && MustErrFlags.find(EEMap[edge]) != MustErrFlags.end()) {
			edgeFlag = EEMap[edge];
			return;
		}

	// Process fn logging that capture the error level
	for (auto edge : EdgeSet) 
		if (EEMap[edge] && LogErrFlags.find(EEMap[edge]) != LogErrFlags.end()) {
			edgeFlag = EEMap[edge];
			return;
		}

	// Any edge other than zero and May_Return_Error
	for (auto edge : EdgeSet) 
		if (EEMap[edge] && EEMap[edge] != 2) {
			edgeFlag = EEMap[edge];
			return;
		}

	assert(false && "Missing MustError branches");
	return;
}

// Determine severity by checking for logging functions that have a severity
// level embedded in their names
void ExaggerateErrPass::searchLoggingFn(BBPath &BP, bool &isReturned,
				std::set<BasicBlock *> &visitedBB, HandlePair &hpair) {

	uint8_t tmp_var = hpair.first;

	for (BasicBlock *BB : BP) {
		// Skip enumerating duplicate BB
		if (visitedBB.find(BB) != visitedBB.end())
			continue;
		visitedBB.insert(BB);

		for (Instruction &i : *BB) {
			Instruction *I = &i;

			// If the path returns the error to caller
			if (isa<ReturnInst>(I))
				isReturned = true;

			CallInst *CI = dyn_cast<CallInst>(I);
			if (!CI) continue;

			// Check if we already evaluated this particular CallInst
			if (CallSeverityMap.find(CI) != CallSeverityMap.end()) {
				tmp_var = CallSeverityMap[CI];

			} else {
				StringRef FuncName = getCalledFuncName(CI);
				if (FuncName.find("llvm") != std::string::npos || FuncName.empty())
					continue;

				string funcName = FuncName.str();
				// Eliminate IS_ERR, PTR_ERR, and like cases
				if (SeverityNameSet.find(funcName) != SeverityNameSet.end()) 
					continue;

				if (FuncName.endswith("printk")) 
					funcName = getSourceFuncName(CI);

				tmp_var = getCallSiteSeverity(CI, funcName);
				CallSeverityMap[CI] = tmp_var;
			}

			// Update the severity level to the more severe one possible
			if (hpair.first > tmp_var) {
				hpair.first = tmp_var;
				hpair.second = CI;
			}
		}
	}
}

// Depth First Search of the basic blocks starting from the error block
void ExaggerateErrPass::DFS(BasicBlock *BB, BBPath &Path, 
			set<BasicBlock*> &reachBB, std::set<BBPath>& PathSet, 
			SecurityChecksPass::EdgeErrMap &EEMap, unsigned flag) {

	// Heuristic to avoid path explosion of BB
	Instruction *TI = BB->getTerminator();
	if (PathSet.size() > 100)
		return;

	if (reachBB.find(BB) != reachBB.end())
		return;
	reachBB.insert(BB);
	Path.push_back(BB);

	succ_iterator si = succ_begin(BB), se = succ_end(BB);
	if (si == se)
		PathSet.insert(Path);

	bool FoundSucc = false;
	for (; si != se; ++si) {
		SecurityChecksPass::CFGEdge Edge = std::make_pair(TI, *si);	
		if (EEMap.find(Edge) == EEMap.end() && EEMap[Edge] != flag)
			continue;

		FoundSucc = true;
		DFS(*si, Path, reachBB, PathSet, EEMap, flag);
	}

	if (!FoundSucc)
		PathSet.insert(Path);

	BasicBlock *BB_t = Path.back();
	Path.pop_back();
	reachBB.erase(BB_t);
}

// Filter cases in ErrorCountMap having same level err handling
// and all those having error handling below the average level
void ExaggerateErrPass::removeUninterstingRecords() {

	unsigned before = ErrorCountMap.size();
	for (auto it = ErrorCountMap.begin(), ite = ErrorCountMap.end();
			it != ite; ) {
		HandleList &HList = (*it).second.first;
		FreqVector FV(NumLevels);

		// Build a FreqVector representation of the HandleList
		for (auto &x : HList)
			FV[x.first] += 1;

		unsigned count_nz = 0, sum = 0;
		unsigned max_idx = std::distance(FV.begin(), std::max_element(
						FV.begin(), FV.end()));
		unsigned max_value = FV[max_idx];

		for (auto &x : FV) {
			if (x)
				++count_nz;
			sum += x;
		}

		// Single error handling case or no error handling detected
		if (count_nz <= 1 || !sum) {
			it = ErrorCountMap.erase(it);
			continue;
		}

		// Strategy: The default handling severity is greater than threshold
		if (sum && static_cast<float>(max_value) / sum < threshold) {
			it = ErrorCountMap.erase(it);
			continue;
		}

		// If the "outlier" error is handled at a lower level
		sum = 0;
		for (unsigned i = 0; i < max_idx; ++i) 
			sum += FV[i];
		if (!sum) {
			it = ErrorCountMap.erase(it);
			continue;
		}

		ErrorCountMap[it->first] = std::make_pair(HList, max_idx);
		++it;
	}

#ifdef DEBUG_PRINT
	OP << "\nClean up insignificant records in ErrorCountMap\n" 
		<< "Before: " << before << "\tAfter: " << 
		ErrorCountMap.size() << "\n";
#endif
}

// The second phase of identifying outlier cases
void ExaggerateErrPass::performStatisticalAnalysis() {

	OP << EFList.size() << " error records within " 
		<< ErrorCountMap.size() << " types \n";
	for (ErrorFactors EF : EFList) {

		SecurityCheck *SC = EF.getSecurityCheck();
		string spatial = EF.getSpatialCtx();
		unsigned temporal = EF.getTemporalCtx();
		std::set<err_t> ErrorSet = EF.getErrorSet();

		for (auto err : ErrorSet) {
			std::set<int> ErrValues;
			ValueToInt(&err, ErrValues);

			if (ErrValues.empty())
				continue;

			for (int value_int : ErrValues) {
				if (value_int == DEFLTVAL)
					continue;

				struct ErrorRecord ER(value_int, spatial, temporal);
				validateEEBug(ER, SC);
			}
		}
	} // End iterating over the ErrorFactors & SecurityChecks
}

// Validate and store if Error Record is an EE Bug
void ExaggerateErrPass::validateEEBug(ErrorRecord &ER, SecurityCheck *SC) {

	// If the error is in ErrorCountMap and the security check is processed
	if (ErrorCountMap.find(ER) == ErrorCountMap.end())
		return;

	if (ScHandleMap.find(SC) == ScHandleMap.end())
		return;

	HandleList &SList = ScHandleMap[SC];
	if (SList.empty())
		return;

	HListMaxPair HMP = ErrorCountMap[ER];	
	unsigned sum = 0;
	FreqVector FV(NumLevels);
	unsigned level = HMP.second;
	HandleList &HList = HMP.first;

	for (auto &n : HList) {
		sum += n.first;
		FV[n.first] += 1;
	}

#ifdef SEVERE_ERR
	level = (severeErrLevel < level) ? severeErrLevel : level;
#endif

	auto si = SList.begin(), se = SList.end();
	for (auto &x : HList) {
		if (x.first >= level)
			continue;

		if (std::find(si, se, x) == se)
			continue;

		auto pair = std::make_pair(SC, x.first);
		if (ResultSet.find(pair) != ResultSet.end())
			continue;
		ResultSet.insert(pair);

#ifdef PRINT_RESULT
		Value *V = isa<PHINode>(SC->getSCheck()) ?
			SC->getSCBranch() : SC->getSCheck();

		printSourceCodeInfo(V);
		OP << "Error_: " << ER.Error;

		//OP << "\ndbg_lvl: " << i << " " << level;
		OP << "\nSecurity Check: " << *V
			<< "\nSpatial: " << ER.spatialCtx 
			<< ", Temporal: " << ER.temporalCtx
			<< "\nEx_level: " << x.first << "\nSeverity: " << 
			static_cast<float>(FV[x.first])/sum 
			<< "\nFreqVector: ";
		for (unsigned i = 0 ; i < NumLevels; ++i)
			OP << (unsigned)FV[i] << " ";
		OP	<< "\nHandler ";
		printSourceCodeInfo(x.second);
		OP << "\n";
#endif
	}

}

// For each security check, update the errors it handles
void ExaggerateErrPass::updateErrorCounts (ErrorFactors *EF) {

	string spatial = EF->getSpatialCtx();
	unsigned temporal = EF->getTemporalCtx();
	SecurityCheck *SC = EF->getSecurityCheck();
	std::set<err_t> ErrorSet = EF->getErrorSet();
	HandleList& HList = ScHandleMap[SC];

	// Store the results for phase 1
	for (auto err : ErrorSet) {
		std::set<int> ErrValues;
		ValueToInt(&err, ErrValues);

		if (ErrValues.empty())
			continue;

		for (int value_int : ErrValues) {
			// TODO(APK): if the value is a function name ??
			if (value_int == DEFLTVAL)
				continue;

			// Evaluate the importance of contexts, uncomment as necessary
			// spatial = "";
			// temporal = 0;
			struct ErrorRecord ER(value_int, spatial, temporal);

			if (ErrorCountMap.find(ER) != ErrorCountMap.end()) {
				HandleList &FHList = (ErrorCountMap[ER]).first;
				for (auto &x : HList)
					FHList.push_back(x);
				ErrorCountMap[ER] = std::make_pair(FHList, 0);
			} else {
				ErrorCountMap[ER] = std::make_pair(HList, 0);
			}
		}
	} // End of source iterations
}

// For each call site return the severity of the error, targeting specifically
// printk and pr_err type functions
uint8_t ExaggerateErrPass::getCallSiteSeverity(CallInst *CI, 
					std::string& FuncName) {
	uint8_t severity = DEFAULT;
	smatch match;

	if (WarnErrorSet.find(FuncName) != WarnErrorSet.end())
		return 1;
		
	if (FuncName.find(' ') != std::string::npos)
		FuncName = FuncName.substr(0, FuncName.find(' '));

	// Get the severity using printk function followed by a level
	// handles cases such as pr_err(
	if (FuncName.find("printk") != std::string::npos) {
		string line;
		getSourceCodeLine(CI, line);

		// check for the last word in the function name
		if (regex_search(line, match, print_pattern)) {
			std::size_t found = match[0].str().find_last_of("_");
			if (found != std::string::npos)
				severity = stringToErrLevel(uppercase(
						match[0].str().substr(found+1)));
		}

		if (severity != DEFAULT)
			return severity;

		// printk(KERN_INFO ...
		static const std::regex err_level("KERN_([A-Z]+)");
		if (regex_search(line, match, err_level)) 
			severity = stringToErrLevel(match[1]);

		if (severity != DEFAULT)
			return severity;
	}

	// Check for panic and other functions having error within the func name
	static const std::regex uscore("_");

	auto FIter = ErrorTermSet.find(FuncName);
	if (FIter != ErrorTermSet.end()) {
		sregex_token_iterator iter((*FIter).begin(), (*FIter).end(), uscore, -1);
		sregex_token_iterator end;
		for (; iter != end; ++iter) {
			severity = stringToErrLevel(uppercase(*iter));
			if (severity != DEFAULT)
				return severity;
		}

		severity = 0;
		return severity;
	}

	// Check for BUG, BUG_ON, ASSERT cases
	string line;
	getSourceCodeLine(CI, line);

	if (regex_search(line, match, func_pattern)) {
		FIter = ErrorTermSet.find(match[0].str());
		if (FIter != ErrorTermSet.end()) {

			// Severity within filename
			sregex_token_iterator iter((*FIter).begin(), (*FIter).end(), uscore, -1);
			sregex_token_iterator end;
			for (; iter != end; ++iter) {
				severity = stringToErrLevel(uppercase(*iter));
				if (severity != DEFAULT)
					return severity;
			}

			severity = 0;
			return severity;
		}
	}

	// Worst case: Severity anywhere in the string name
	sregex_token_iterator iter(FuncName.begin(), FuncName.end(), uscore, -1);
	sregex_token_iterator end;
	for (; iter != end; ++iter) {
		severity = stringToErrLevel(uppercase(*iter));
		if (severity != DEFAULT)
			return severity;
	}

	return severity;
}

// Perform backward traversal from the returnInst to determine error values
void ExaggerateErrPass::performEEBackwardAnalysis(Function *F, 
		 Value *V, std::set<Value *> &EVSet, std::set<Value *> &Visited) {

	if (Visited.find(V) != Visited.end())
		return;
	Visited.insert(V);

	if (CallInst *CI = dyn_cast<CallInst>(V)) {
		string FName = static_cast<std::string>(getCalledFuncName(CI));
		if (SeverityNameSet.find(FName) == SeverityNameSet.end())
			EVSet.insert(V);
		else 
			performEEBackwardAnalysis(F, CI->getOperand(0), EVSet, Visited);
		return;
	}

	// Check if it is an error value
	if (dyn_cast<Constant>(V)) {
		if (SCP.isValueErrno(V, F))
			EVSet.insert(V);
		return;
	}

	if (isa<Argument>(V))
		return;

	if (isa<LoadInst>(V)) {
		LoadInst* LI = dyn_cast<LoadInst>(V);
		if (LPSet.find(LI->getPointerOperand()) != LPSet.end())
			return;
		else
			LPSet.insert(LI->getPointerOperand());

		for (auto i = inst_begin(F), e = inst_end(F); i != e; ++i) {
			StoreInst *SI = dyn_cast<StoreInst>(&*i);
			if (!SI)
				continue;
			if (!DFA.possibleUseStResult(LI, SI)) 
				continue;
			if (SI->getPointerOperand() != LI->getPointerOperand()) 
				continue;
			performEEBackwardAnalysis(F, SI->getValueOperand(), EVSet, Visited);
		}
		return;
	}

	if (isa<UnaryInstruction>(V)) {
		UnaryInstruction *UI = dyn_cast<UnaryInstruction>(V);
		performEEBackwardAnalysis(F, UI->getOperand(0), EVSet, Visited);
		return;
	}

	if (isa<BinaryOperator>(V)) {
		BinaryOperator *BI = dyn_cast<BinaryOperator>(V);
		performEEBackwardAnalysis(F, BI->getOperand(0), EVSet, Visited);
		performEEBackwardAnalysis(F, BI->getOperand(1), EVSet, Visited);
		return;
	}

	if (isa<ICmpInst>(V)) {
		ICmpInst *CI = dyn_cast<ICmpInst>(V);
		performEEBackwardAnalysis(F, CI->getOperand(0), EVSet, Visited);
		performEEBackwardAnalysis(F, CI->getOperand(1), EVSet, Visited);
		return;
	}

	if (isa<FCmpInst>(V)) {
		FCmpInst *CI = dyn_cast<FCmpInst>(V);
		performEEBackwardAnalysis(F, CI->getOperand(0), EVSet, Visited);
		performEEBackwardAnalysis(F, CI->getOperand(1), EVSet, Visited);
		return;
	}

	PHINode *PN = dyn_cast<PHINode>(V);
	if (PN) {
		for (unsigned i = 0, e = PN->getNumIncomingValues(); i != e; ++i) {
			Value *IV = PN->getIncomingValue(i);
			performEEBackwardAnalysis(F, IV, EVSet, Visited);
		}
		return;
	}

	if (isa<GetElementPtrInst>(V)) {
		GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(V);
		performEEBackwardAnalysis(F, GEP->getPointerOperand(), EVSet, Visited);
		return;
	}

	if (isa<SelectInst>(V)) {
		SelectInst *SI = dyn_cast<SelectInst>(V);
		performEEBackwardAnalysis(F, SI->getTrueValue(), EVSet, Visited);
		performEEBackwardAnalysis(F, SI->getFalseValue(), EVSet, Visited);
		return;
	}

	if (dyn_cast<ExtractElementInst>(V) ||
		dyn_cast<InsertElementInst>(V)  ||
		dyn_cast<ExtractValueInst>(V)   ||
		dyn_cast<InsertValueInst>(V)    ||
		dyn_cast<ShuffleVectorInst>(V))
		return;

	OP << "== Warning: unsupported LLVM IR:" << *V <<  " in " 
		<< F->getName() << "\n";

#ifdef DEBUG_PRINT
	assert(0);
#endif
}

// Helper function to transform the string to a warning level
uint8_t ExaggerateErrPass::stringToErrLevel (std::string s) {
	std::size_t nfound = std::string::npos;

	if (s.find("EMERG") != nfound) return CRIT;
	else if (s.find("CRIT") != nfound) return CRIT;
	else if (s.find("ALERT") != nfound) return CRIT;
	else if (s.find("ERR") != nfound) return ERR;
	else if (s.find("WARN") != nfound) return WARNING;
	else if (s.find("NOTICE") != nfound) return WARNING;
	else if (s.find("INFO") != nfound) return WARNING;
	else if (s.find("DBG") != nfound || s.find("DEBUG") != nfound) 
		return DEBUG;

	return DEFAULT;
}

string ExaggerateErrPass::uppercase(std::string s) {
	std::string str = s;
	std::transform(str.begin(), str.end(),str.begin(), ::toupper);
	return str;
}

// Translate the Value to an int to avoid type based issues such as 
// i32 -1 vs i64 -1
void ExaggerateErrPass::ValueToInt(err_t *err, std::set<int> &ErrValues) {

	if (err->first != DEFLTVAL) {
		ErrValues.insert(err->first);
		return;
	}
		
	// Recursively identify errors within each function found in ErrorSet
	std::list<Value *> EFnList;
	std::set<Value *> VisitedSet;

	EFnList.push_back(err->second);
	while (!EFnList.empty()) {

		Value *V = EFnList.front();
		EFnList.pop_front();

		if (VisitedSet.count(V) != 0)
			continue;
		VisitedSet.insert(V);

		if (isa<ConstantPointerNull>(V)) {
			ErrValues.insert(NULLVAL);
			continue;
		}

		if (ConstantInt *CI = dyn_cast<ConstantInt>(V)) {
			ErrValues.insert(CI->getValue().getSExtValue());
			continue;
		}

		Function *F = dyn_cast<Function>(V);
		if (!F) {
			// TODO(APK): Args, indirect calls, asm,...
			continue;
		}

		// Process the function
		if (Ctx->UnifiedFuncSet.find(F) == Ctx->UnifiedFuncSet.end()) 
			continue;

		if (FnRvalMap.find(F) == FnRvalMap.end()) 
			continue;

		std::set<Value *> FnErrSet = FnRvalMap[F];
		for (Value *E : FnErrSet) 
			EFnList.push_back(E);
	}
}

bool ExaggerateErrPass::copyErrors(Function *F, SecurityCheck *SC,
												set<err_t> &ErrSet) {
	set<Value *> CTSet;
	Value *Check = SC->getSCheck();
	identifyTargets(Check, CTSet);

	if (CTSet.empty())
		return false;

	// Just determine if the src is a copy_from_user CallInst
	for (auto CT : CTSet) {

		CallInst *CI = dyn_cast<CallInst>(CT);
		if (!CI) continue;
		Function *CF = CI->getCalledFunction();
		if (!CF) continue;
		string FName = static_cast<std::string>(CF->getName());

		if (FName.find("copy_from_user") != string::npos) {
			err_t Err = std::make_pair(DEFLTVAL, CI);
			ErrSet.insert(Err);
			return true;
		}
	}

	return false;
}
