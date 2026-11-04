#include <reuse_summary_concurrent_unit.h>

#include <cstdlib>
#include <iostream>

int main() {
  // churn 3 shared = 3 * len (Cons 0 (build 4)) = 15
  if (ReuseSummaryConcurrentUnit::total != 15u) {
    std::cerr << "total = " << ReuseSummaryConcurrentUnit::total << "\n";
    return EXIT_FAILURE;
  }
  for (int i = 0; i < 5; ++i) {
    ReuseSummaryConcurrentUnit::run(std::monostate{});
  }
  return 0;
}
