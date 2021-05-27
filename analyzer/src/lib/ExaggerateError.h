#ifndef ANALYZER_SRC_LIB_EXAGGERATEERROR_H_
#define ANALYZER_SRC_LIB_EXAGGERATEERROR_H_

#include <llvm/ADT/SmallVector.h>
#include "Common.h"
#include "Analyzer.h"
#include "SecurityChecks.h"
#include "DataFlowAnalysis.h"

#include <set>
#include <map>
#include <list>
#include <string>
#include <vector>
#include <utility>

enum Severity {
	EMERG, /* = 0 */
//	ALERT,
	CRIT,
	ERR,
	WARNING,
//	NOTICE,
//	INFO,
	DEBUG,
	DEFAULT /* = 6*/
};

enum TemporalFunc {
	REGULAR,  // 0
	INIT,     // 1
	EXIT      // 2
};

enum SpecialRetVal {
	NULLVAL = -0xDEADBEEF,
	ALLOCVAL = -0xBAADCAFE,
	DEFLTVAL = 123456
};

// Assembly functions, prone to errors
static vector<string> ErrAsmVector = {
	"xchg",
	"cmpxchg",
	"get_user",
	"put_user",
	"this_cpu_ptr",
	"this_cpu_read",
	"assign_in_user",
	"check_user_mbz",
	"smp_processor_id",
	"FAT_IOCTL_FILLDIR_FUNC",
};

static std::set<string> SeverityNameSet = {
	"IS_ERR", "PTR_ERR", "ERR_PTR", "IS_ERR_OR_NULL",
	"PTR_ERR_OR_ZERO", "ERR_CAST",
};

static std::set<string> ErrorTermSet = {
	"BUG", "BUG_ON", "ASM_BUG", "panic", "ASSERT", "assert",
	"kernel_halt", "kernel_power_off", "signal_fault", "WARN_ON",
};

static std::set<string> WarnErrorSet = {
	"WARN_ON", "WARN", "WARN_ONCE", "WARN_ON_ONCE"
};

static std::set<string> RefinedSet = {"fs", "drivers", "net"};
// Account for error sources
typedef pair<int, Value *> err_t;

const unsigned NumLevels = 6;
// Vector which internally represents the number of occurences an
// error is handled at a severity level, indexed by the enum Severity
typedef llvm::SmallVector<uint8_t, NumLevels> FreqVector;

struct ErrorRecord {
	int Error;
	string spatialCtx;
	unsigned temporalCtx;

	ErrorRecord(int E, string s, unsigned t) {
		Error = E;
		spatialCtx = s;
		temporalCtx = t;
	}

	~ErrorRecord() { }

	friend bool operator< (const struct ErrorRecord &ER1,
				const struct ErrorRecord &ER2) {
		return (ER1.Error < ER2.Error);
	}
};

typedef std::list<BasicBlock* > BBPath;
typedef std::pair<unsigned, Value *> HandlePair;
typedef std::list<HandlePair> HandleList;
typedef std::pair<HandleList, unsigned> HListMaxPair;

// Class to account for the errors per security check
class ErrorFactors {
	public:
	ErrorFactors() {
		TemporalCtx = 0;
		SpatialCtx = "";
	}

	explicit ErrorFactors(SecurityCheck *SCheck) : SC(SCheck) {
		ErrorFactors();
	}

	ErrorFactors(const set<err_t> &s, string dir, unsigned time,
			SecurityCheck *SCheck) :
		ErrorSet(s), SpatialCtx(dir), TemporalCtx(time),
		SC(SCheck){
	}

	~ErrorFactors() {
	}

	set<err_t>& getErrorSet() { return ErrorSet; }

	string&  getSpatialCtx() { return SpatialCtx; }

	SecurityCheck* getSecurityCheck() { return SC; }

	unsigned getTemporalCtx() { return TemporalCtx; }

	void setSpatialCtx(string dir) { SpatialCtx = dir; }

	void setTemporalCtx(unsigned time) { TemporalCtx = time; }

	void setSecurityCheck(SecurityCheck *Check) { SC = Check; }

	friend bool operator< (const ErrorFactors &EF1, const ErrorFactors &EF2) {
		return (EF1.SpatialCtx < EF2.SpatialCtx);
	}

	void printEFContents() {
		OP << "\n";
		printSourceCodeInfo(SC->getSCheck()); 
		OP << "== SCheck:       " << *(SC->getSCheck()) << "\n"
		<< "== Spatial Ctx:  " << SpatialCtx << "\n"
		<< "== Temporal Ctx: " << TemporalCtx << "\n"
		<< "== ErrorSet Size:  " << ErrorSet.size() << " \n";
	}

	private:
	// Error, its context, security check
	set<err_t> ErrorSet;
	unsigned TemporalCtx;
	string SpatialCtx;
	SecurityCheck *SC;

};

class ExaggerateErrPass : public IterativeModulePass {

	public:
	static list<ErrorFactors> EFList;
	static std::set<StringRef> InitFuncSet;
	static std::set<StringRef> ExitFuncSet;
	static map<SecurityCheck *, HandleList> ScHandleMap;
	static map<Function *, std::set<Value *>> FnRvalMap;
	static map<CallInst *, SecurityCheck *> CallerSCkMap;
	static map<struct ErrorRecord, HListMaxPair> ErrorCountMap;
	static set<std::pair<SecurityCheck *, unsigned>> ResultSet;

	private:
		unsigned MIdx;
		DataFlowAnalysis DFA;
		SecurityChecksPass SCP;
		std::set<Value *> LPSet; 

		// Collect InitFunctions and their callers
		void checkFuncSection(Function *);

		// Collect Exit Functions and their callees
		void checkFunctionExit(Function *);

		void identifyTargets(Value *, set<Value *> &);

		// get severity level of a callsite
		uint8_t getCallSiteSeverity(CallInst *, std::string &);

		// fill the structure given a security check 
		bool determineErrors(Function *, SecurityCheck *, ErrorFactors &);
		bool copyErrors(Function *, SecurityCheck *, std::set<err_t>  &);

		bool backtrackSource(Function *, Instruction *, set<err_t> &); 

		// Second level of error identification
		bool evaluatePredicate(Function *, Instruction *, set<err_t> *);

		bool getSpatialCtx(const string &, string &);

		unsigned getTemporalCtx(Function &);

		// InterProcedural error severity determination
		void ExtractErrorSeverity(Function *, SecurityCheck *, 
					SecurityChecksPass::EdgeErrMap &, HandleList &);

		void DFS(BasicBlock*, BBPath &, set<BasicBlock *> &, std::set<BBPath> &,
				SecurityChecksPass::EdgeErrMap &, unsigned);

		void searchLoggingFn(BBPath &, bool &, set<BasicBlock *> &, 
				HandlePair &);

		// Translate value to an int
		void ValueToInt(err_t *, std::set<int> &);

		// Intraprocedural analysis - determine which block contains the error
		void determineErrorBlock(SecurityCheck *, 
				SecurityChecksPass::EdgeErrMap &, unsigned &);

		// Determine how the error is handled intra procedurally
		void determineErrorReturn(Value *, std::set<Value *> &, bool *);

		// Perform inter procedural analysis to determine the error handling site
		void forwardInterErrHandling(Function *, Value *, 
					std::set<Function*> &, HandleList &);

		// Perfom intra procedural backward analysis to determine return error val
		void performEEBackwardAnalysis(Function *, Value *, set<Value *> &,
				std::set<Value *> &);

		// Collect all errors returning from a particular function
		void collectReturnValues(Function *, std::set<Value *> &, 
							std::set<Function *> &);

		// Collect errors from CallInst
		void collectErrorCallInst(CallInst *, set<err_t> &);

		// Collect errors from Constants
		void collectErrorConstants(Function *, Value *, set<err_t> &);

		// update the errors and their corresponding counts
		void updateErrorCounts(ErrorFactors *);

		// remove cases with error handling below threshold
		void removeUninterstingRecords();

		// Phase 2: statistical analysis on the results from P1
		void performStatisticalAnalysis();

		// Validate if the ErrorRectod is an EE Bug
		void validateEEBug(ErrorRecord &, SecurityCheck *);

	public:
	explicit ExaggerateErrPass(GlobalContext *Ctx_)
		: IterativeModulePass(Ctx_, "ExaggerateErr"),
		DFA(Ctx_), SCP(Ctx_) {
			MIdx = 0;
		}

		// Memoization to avoid calling the same CallInst repeatedly
		std::map<CallInst *, uint8_t> CallSeverityMap;

		virtual bool doInitialization(llvm::Module *);
		virtual bool doFinalization(llvm::Module *);
		virtual bool doModulePass(llvm::Module *);
		string uppercase(std::string);
		uint8_t stringToErrLevel(std::string);
};

#endif  // ANALYZER_SRC_LIB_EXAGGERATEERROR_H_
