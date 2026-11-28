// Crane side: hand the bytes of a DIMACS file to the extracted solver, which
// parses and solves them, and report.  Everything but reading the file and
// printing the answer happens in Rocq (Solver.solve_dimacs).  The solver
// reads the bytes through a read-only view, so a std::vector serves; running
// out of fuel throws std::runtime_error.
#include "solver.h"
#include <chrono>
#include <cstdio>
#include <span>
#include <stdexcept>
#include <vector>

int main(int argc, char **argv) {
  if (argc < 2) return 2;
  std::FILE *f = std::fopen(argv[1], "rb");
  if (!f) { std::perror(argv[1]); return 2; }
  std::vector<uint64_t> bytes;
  unsigned char buf[1 << 16];
  size_t n;
  while ((n = std::fread(buf, 1, sizeof buf, f)) > 0)
    bytes.insert(bytes.end(), buf, buf + n);
  bool err = std::ferror(f);
  std::fclose(f);
  if (err) { std::perror(argv[1]); return 2; }
  const uint64_t big = uint64_t(1) << 62;
  // At most one conflict per step, so code + 8 * conflicts stays below 2^62.
  const uint64_t budget = uint64_t(1) << 58;
  auto t0 = std::chrono::steady_clock::now();
  uint64_t r;
  try {
    r = Solver::solve_dimacs(big, budget, std::span<const uint64_t>(bytes),
                             bytes.size());
  } catch (const std::runtime_error &) {
    r = 2;
  }
  double secs = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
  static const char *names[] = {"UNSAT", "SAT", "UNKNOWN", "BADMODEL",
                                "INVALID", "?", "?", "?"};
  std::printf("%s conflicts=%llu time=%.4f\n", names[r % 8],
              (unsigned long long)(r / 8), secs);
  return 0;
}
