This version of CompCert includes a profiling system. It tells CompCert's optimization phases for each conditional branch instruction which of the two branches was more frequently taken. This system is not available for all combinations of target architecture and operating system; see below.

For using this profiling system one has to
1. Compile a special version of the program that will count, for each branch, the number of times it was taken, and recording this information to a file.
2. Execute this special version on representative examples. It will record the frequencies of execution of branches to a log file.
3. Recompile the program, telling CompCert to use the information in the log file.

This system does not use the same formats as gcc's gcov profiles, since it depends heavily on compiler internals. It seems however possible to profile and optimize programs consisting of modules compiled with gcc and CompCert by using both system simultaneously: compiler uses separate log files.

To compile the special version that logs frequencies to files, use the option `-fprofile-arcs`. This option has to be specified at compile time but is not needed at link time (however, a reminder: if you link using another compiled than CompCert, you need to link against `libcompcert.a`). You may mix object files compiled with and without this option.

This version may experience significant slowdown compared to normally compiled code, so do not use `-fprofile-arcs` for production code.

At the end of execution of the program, frequency information will be logged to a file whose default name is `compcert_profiling.dat` (in the current directory). Another name may be used by specifying it using the `COMPCERT_PROFILING_DATA` environment variable. If this variable contains an empty string, no logging is done (but the slowdown still applies).

Data are appended to the log file, never deleted, so it is safe to run the program several times on several test cases to accumulate data.

Depending on the platform, this logging system is or is not thread-safe and is or is not compatible with position-independent code (PIC). In non thread-safe configurations, if two different execution threads execute code to be profiled, the profiling counters may end up with incorrect values.

| Target platform | Available? | Thread-safe | PIC |
|-----------------|------------|-------------|-----|
| AArch64         | Yes        | Yes         | No  |
| ARM             | Yes        | No          | No  |
| IA32            | Yes        | No          | No  |
| KVX             | Yes        | Yes         | No  |
| PowerPC         | No         |             |     |
| PowerPC 64      | No         |             |     |
| Risc-V 32       | No         |             |     |
| Risc-V 64       | No         |             |     |
| x86-64          | Yes        | Yes         | Yes |

For recompiling the program using profiling information, use `-fprofile-use= compcert_profiling.dat -ftracelinearize` (substitute the appropriate filename for `compcert_profiling.dat` if needed). Experiments show performance improvement on KVX, not on other platforms.

The same options (except for `-fprofile-use=` and `-fprofile-arcs`) should be used to compile the logging and optimized versions of the program: only functions that are exactly the same in the intermediate representation will be optimized according to profiling information.
