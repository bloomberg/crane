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
  // At most one conflict per step, so code + 4 * conflicts stays below 2^61.
  const uint64_t budget = uint64_t(1) << 59;
  auto t0 = std::chrono::steady_clock::now();
  uint64_t r;
  try {
    r = Solver::solve(big, budget, nvars, input, input.len());
  } catch (const satbench::out_of_fuel &) {
    r = 2;
  }
  double secs = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
  static const char *names[] = {"UNSAT", "SAT", "UNKNOWN", "BADMODEL"};
  std::printf("%s conflicts=%llu time=%.4f\n", names[r % 4],
              (unsigned long long)(r / 4), secs);
  return 0;
}
