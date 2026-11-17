// Driver for one Gb* workload: `WORKLOAD.exe N ROUNDS` prints the workload's
// checksum and the seconds it took.  A wrapper includes the workload's header
// and defines WL_CALL before including this file.
#include <chrono>
#include <cstdio>
#include <cstdlib>

int main(int argc, char **argv) {
  if (argc != 3) {
    std::fprintf(stderr, "usage: %s N ROUNDS\n", argv[0]);
    return 2;
  }
  uint64_t n = std::strtoull(argv[1], nullptr, 10);
  uint64_t rounds = std::strtoull(argv[2], nullptr, 10);
  auto t0 = std::chrono::steady_clock::now();
  uint64_t r = WL_CALL(n, rounds);
  double s = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
  std::printf("%llu time=%.4f\n", (unsigned long long)r, s);
  return 0;
}
