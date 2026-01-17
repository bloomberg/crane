#include <ack.h>
#include <algorithm>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>

unsigned int Ack::ack(const unsigned int m, const unsigned int n) {
  std::function<unsigned int(unsigned int)> ack_m;
  ack_m = [&](unsigned int n0) -> unsigned int {
    if (m <= 0) {
      return (n0 + 1);
    } else {
      unsigned int pm = m - 1;
      if (n0 <= 0) {
        return ack(pm, 1u);
      } else {
        unsigned int pn = n0 - 1;
        return ack(pm, ack_m(pn));
      }
    }
  };
  return ack_m(n);
}
