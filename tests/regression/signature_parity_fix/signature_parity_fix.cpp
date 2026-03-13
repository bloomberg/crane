#include <signature_parity_fix.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

__attribute__((pure)) unsigned int
SignatureParityFix::f(const unsigned int seed) {
  std::function<unsigned int(unsigned int)> aux;
  aux = [&](unsigned int n) -> unsigned int {
    if (n <= 0) {
      return seed;
    } else {
      unsigned int n_ = n - 1;
      return aux(n_);
    }
  };
  return aux((seed + 1));
}
