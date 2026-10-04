#include "thread.h"

void threadtest::fun1(uint64_t n) {
  if (n <= 0) {
    std::cout << std::string("fun1 is done!!!") << '\n';
    return;
  } else {
    uint64_t n0 = n - 1;
    std::cout << std::string("fun1 is sleeping for 100ms") << '\n';
    std::this_thread::sleep_for(std::chrono::milliseconds(INT64_C(100)));
    fun1(n0);
    return;
  }
}

void threadtest::fun2(uint64_t n) {
  if (n <= 0) {
    std::cout << std::string("fun2 is done!!!") << '\n';
    return;
  } else {
    uint64_t n0 = n - 1;
    std::cout << std::string("fun2 is sleeping for 150ms") << '\n';
    std::this_thread::sleep_for(std::chrono::milliseconds(INT64_C(150)));
    fun2(n0);
    return;
  }
}

void threadtest::test(uint64_t m, uint64_t n) {
  std::thread t1 = std::thread(fun1, m);
  std::thread t2 = std::thread(fun2, n);
  t1.join();
  t2.join();
  return;
}

void threadtest::test_pure(uint64_t m, uint64_t n) {
  test(m, n);
  return;
}
