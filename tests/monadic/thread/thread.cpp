#include <thread.h>

#include <chrono>
#include <cstdint>
#include <iostream>
#include <string>
#include <thread>
#include <type_traits>
#include <variant>

void threadtest::fun1(const unsigned int n) {
  if (n <= 0) {
    std::cout << "fun1 is done!!!"s << '\n';
    return;
  } else {
    unsigned int n0 = n - 1;
    std::cout << "fun1 is sleeping for 100ms"s << '\n';
    std::this_thread::sleep_for(std::chrono::milliseconds(int64_t(100)));
    {
      fun1(n0);
      return;
    }
  }
}

void threadtest::fun2(const unsigned int n) {
  if (n <= 0) {
    std::cout << "fun2 is done!!!"s << '\n';
    return;
  } else {
    unsigned int n0 = n - 1;
    std::cout << "fun2 is sleeping for 150ms"s << '\n';
    std::this_thread::sleep_for(std::chrono::milliseconds(int64_t(150)));
    {
      fun2(n0);
      return;
    }
  }
}

void threadtest::test(const unsigned int m, const unsigned int n) {
  std::thread t1 = std::thread(fun1, m);
  std::thread t2 = std::thread(fun2, n);
  t1.join();
  t2.join();
  return;
}

void threadtest::test_pure(const unsigned int m, const unsigned int n) {
  test(m, n);
  return;
}
