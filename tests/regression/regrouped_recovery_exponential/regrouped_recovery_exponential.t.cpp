#include <regrouped_recovery_exponential.h>

#include <csignal>
#include <cstdint>
#include <iostream>
#include <unistd.h>

int main() {
  std::signal(SIGALRM, [](int) {
    const char msg[] = "timeout: lvl 40 did not finish in 20 s\n";
    (void)!write(2, msg, sizeof msg - 1);
    _exit(1);
  });
  alarm(20);
  uint64_t small = RegroupedRecoveryExponential::lvl(10);
  std::cout << "lvl 10 = " << small << std::endl;
  if (small != 1024) return 1;
  uint64_t v = RegroupedRecoveryExponential::lvl(40);
  std::cout << "lvl 40 = " << v << std::endl;
  return v == (uint64_t(1) << 40) ? 0 : 1;
}
