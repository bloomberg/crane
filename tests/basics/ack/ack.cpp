#include <ack.h>

#include <functional>
#include <memory>
#include <type_traits>

__attribute__((pure)) unsigned int Ack::ack(unsigned int m,
                                            const unsigned int &n) {
  std::function<unsigned int(unsigned int)> ack_m;
  ack_m = [&](unsigned int n0) -> unsigned int {
    if (m <= 0) {
      return (n0 + 1);
    } else {
      unsigned int pm = m - 1;
      if (n0 <= 0) {
        return ack(pm, Nat::one);
      } else {
        unsigned int pn = n0 - 1;
        return ack(pm, ack_m(pn));
      }
    }
  };
  return ack_m(n);
}
