# Eecatch: Exaggerated Error Handling Hurts! An In-Depth Study and Context-Aware Detection

Exaggerated Error Handling (EEH) bugs is a class of semantic bugs in software programs where the error-handling level is higher than the intended level. 
These bugs are particularly common in OS kernels because error levels are not uniformly applied across the codebase and often are left to developers interpretation. 
EEH bugs may cause a variety of critical security consequences, including denial-of-service, control-flow integrity violation, and system crashes.

The tool, Eecatch, can quickly detect EEH bugs in the Linux kernel. It evaluates the spatial and temporal context of the error-handling, and by using an inter-procedural, semantic- and context-aware cross-checking it determines the appropriate error-handling level. We have used Eecatch to find 58 new EEH bugs in the Linux kernel. More details can be found in the paper shown at the bottom.

## How to use Eecatch

### Build LLVM
```sh
	$ cd llvm
	$ ./build-llvm.sh
	# The installed LLVM is of version 10.0.0
```

### Build the analyzer
```sh
	# Build the analysis pass of Eecatch
	$ cd ../analyzer
	$ make
	# Now, you can find the executable, `kanalyzer`, in `build/lib/`
```

### Prepare LLVM bitcode files of OS kernels

* Replace error-code definition files of the Linux kernel with the ones in "encoded-errno"
* The code should be compiled with the built LLVM
* Compile the code with options: -O0 or -O2, -g, -fno-inline
* Generate bitcode files
	- We have our own tool to generate bitcode files: https://github.com/sslab-gatech/deadline/tree/release/work. Note that files (typically less than 10) with compilation errors are simply discarded
	- We also provided the pre-compiled bitcode files - https://github.com/umnsec/linux-bitcode

### Run the analyzer
```sh
	# To analyze a single bitcode file, say "test.bc", run:
	$ ./build/lib/kanalyzer -ee test.bc
	# To analyze a list of bitcode files, put the absolute paths of the bitcode files in a file, say "bc.list", then run:
	$ ./build/lib/kalalyzer -mc @bc.list
```

## More details
* [The Eecatch paper (ACM CCS'20)](https://dl.acm.org/doi/pdf/10.1145/3372297.3417256)
```sh
@inproceedings{pakki2020exaggerated,
  title={Exaggerated Error Handling Hurts! An In-Depth Study and Context-Aware Detection},
  author={Pakki, Aditya and Lu, Kangjie},
  booktitle={Proceedings of the 2020 ACM SIGSAC Conference on Computer and Communications Security},
  pages={1203--1218},
  year={2020}
}

```

