#include <modulo_wrap.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
ModuloWrap::addr12_of_nat(const unsigned int n) {
  return (n % 4096u);
}

__attribute__((pure)) unsigned int
ModuloWrap::byte_of_nat(const unsigned int n) {
  return (n % 256u);
}

__attribute__((pure)) unsigned int
ModuloWrap::nibble_of_nat(const unsigned int n) {
  return (n % 16u);
}

__attribute__((pure)) unsigned int Nat::pow(const unsigned int n,
                                            const unsigned int m) {
  if (m <= 0) {
    return 1u;
  } else {
    unsigned int m0 = m - 1;
    return (n * Nat::pow(n, m0));
  }
}
