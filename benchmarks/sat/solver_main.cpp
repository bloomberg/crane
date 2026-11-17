// Crane side: hand the bytes of a DIMACS file to the extracted solver, which
// parses and solves them, and report.  Everything but reading the file and
// printing the answer happens in Rocq (Solver.solve_dimacs).
#include "solver.h"
#include <chrono>
#include <cstdio>

int main(int argc, char **argv) {
  if (argc < 2) return 2;
  std::FILE *f = std::fopen(argv[1], "rb");
  if (!f) { std::perror(argv[1]); return 2; }
  auto bytes = satbench::make_vec<uint64_t>(0, 0);
  unsigned char buf[1 << 16];
  size_t n;
  while ((n = std::fread(buf, 1, sizeof buf, f)) > 0)
    for (size_t i = 0; i < n; i++) bytes.push(buf[i]);
  bool err = std::ferror(f);
  std::fclose(f);
  if (err) { std::perror(argv[1]); return 2; }
  const uint64_t big = uint64_t(1) << 62;
  // At most one conflict per step, so code + 8 * conflicts stays below 2^62.
  const uint64_t budget = uint64_t(1) << 58;
  auto t0 = std::chrono::steady_clock::now();
  uint64_t r;
  try {
    r = Solver::solve_dimacs(big, budget, bytes);
  } catch (const satbench::out_of_fuel &) {
    r = 2;
  }
  double secs = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
  static const char *names[] = {"UNSAT", "SAT", "UNKNOWN", "BADMODEL",
                                "INVALID", "?", "?", "?"};
  std::printf("%s conflicts=%llu time=%.4f\n", names[r % 8],
              (unsigned long long)(r / 8), secs);
  return 0;
}
