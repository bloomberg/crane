// Crane side: read a DIMACS file, run the extracted solver, report.
#include "dimacs.h"
#include "solver.h"
#include <chrono>

int main(int argc, char **argv) {
  if (argc < 2) return 2;
  uint64_t nvars;
  std::vector<uint64_t> flat;
  if (!read_dimacs(argv[1], nvars, flat)) return 2;
  auto input = satbench::make_vec<uint64_t>(0, 0);
  for (uint64_t x : flat) input.push(x);
  const uint64_t big = uint64_t(1) << 62;
  auto t0 = std::chrono::steady_clock::now();
  uint64_t r = Solver::solve(big, big, nvars, input, input.len());
  double secs = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
  static const char *names[] = {"UNSAT", "SAT", "UNKNOWN", "BADMODEL"};
  std::printf("%s conflicts=%llu time=%.4f\n", names[r % 4],
              (unsigned long long)(r / 4), secs);
  return 0;
}
