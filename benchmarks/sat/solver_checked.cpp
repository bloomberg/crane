// The C++ solver as one translation unit with satbench::vec's bounds checks
// on (build.sh compiles it with ASan/UBSan into solver_cpp_checked.exe).
#define SATBENCH_CHECKED 1
#include "solver.cpp"
#include "solver_main.cpp"
