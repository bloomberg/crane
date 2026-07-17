#include <string>
#include <variant>

#ifndef CRANE_BENCHMARK_FLAG
#error "Crane Benchmark did not forward C++ compiler flags"
#endif

struct BenchmarkMatrix {
  static std::string baseline(std::monostate) { return "same"; }
};
