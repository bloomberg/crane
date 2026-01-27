#include <algorithm>
#include <any>
#include <functional>
#include <future>
#include <iostream>
#include <memory>
#include <optional>
#include <par.h>
#include <string>
#include <utility>
#include <variant>

unsigned int partest::ack(const std::pair<unsigned int, unsigned int> p) {
  std::function<unsigned int(unsigned int, unsigned int)> f;
  f = [&](unsigned int m, unsigned int n) -> unsigned int {
    std::function<unsigned int(unsigned int)> ack_m;
    ack_m = [&](unsigned int n0) -> unsigned int {
      if (m <= 0) {
        return (n0 + 1);
      } else {
        unsigned int pm = m - 1;
        if (n0 <= 0) {
          return f(pm, 1u);
        } else {
          unsigned int pn = n0 - 1;
          return f(pm, ack_m(pn));
        }
      }
    };
    return ack_m(n);
  };
  return f(p.first, p.second);
}

std::pair<unsigned int, unsigned int> partest::fast(const unsigned int m,
                                                    const unsigned int n) {
  std::pair<unsigned int, unsigned int> f = [&](void) {
    std::pair<unsigned int, unsigned int> p = std::make_pair(m, n);
    std::future<unsigned int> t1 = std::async(std::launch::async, ack, p);
    std::future<unsigned int> t2 = std::async(std::launch::async, ack, p);
    unsigned int r1 = t1.get();
    unsigned int r2 = t2.get();
    return std::make_pair(r1, r2);
  }();
  return f;
}

std::pair<unsigned int, unsigned int> partest::slow(const unsigned int m,
                                                    const unsigned int n) {
  std::pair<unsigned int, unsigned int> p = std::make_pair(m, n);
  unsigned int r1 = ack(p);
  unsigned int r2 = ack(p);
  return std::make_pair(r1, r2);
}
