#include <algorithm>
#include <chrono>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <thread.h>
#include <thread>
#include <utility>
#include <variant>

void threadtest::fun1(const unsigned int n) {
  if (n <= 0) {
    std::cout << "fun1 is done!!!" << '\n';
    return;
  } else {
    unsigned int n0 = n - 1;
    std::cout << "fun1 is sleeping for 100ms" << '\n';
    std::this_thread::sleep_for(std::chrono::milliseconds(100));
    return fun1(n0);
  }
}

void threadtest::fun2(const unsigned int n) {
  if (n <= 0) {
    std::cout << "fun2 is done!!!" << '\n';
    return;
  } else {
    unsigned int n0 = n - 1;
    std::cout << "fun2 is sleeping for 150ms" << '\n';
    std::this_thread::sleep_for(std::chrono::milliseconds(150));
    return fun2(n0);
  }
}

void threadtest::test(const unsigned int m, const unsigned int n) {
  std::thread t1 = std::thread(fun1, m);
  std::thread t2 = std::thread(fun2, n);
  t1.join();
  t2.join();
  return;
}

void threadtest::test2(const unsigned int m, const unsigned int n) {
  return test(m, n);
}
