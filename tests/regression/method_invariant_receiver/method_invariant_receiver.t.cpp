#include <method_invariant_receiver.h>

#include <cstdio>

int main() {
  if (MethodInvariantReceiver::deep != 3) {
    std::printf("FAIL: deep = %llu, expected 3\n",
                (unsigned long long)MethodInvariantReceiver::deep);
    return 1;
  }
  std::printf("OK\n");
  return 0;
}
