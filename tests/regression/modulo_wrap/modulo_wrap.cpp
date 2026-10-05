#include "modulo_wrap.h"

uint64_t ModuloWrap::addr12_of_nat(uint64_t n) {
  return (UINT64_C(4096) ? n % UINT64_C(4096) : n);
}

uint64_t ModuloWrap::byte_of_nat(uint64_t n) {
  return (UINT64_C(256) ? n % UINT64_C(256) : n);
}

uint64_t ModuloWrap::nibble_of_nat(uint64_t n) {
  return (UINT64_C(16) ? n % UINT64_C(16) : n);
}

uint64_t Nat::pow(uint64_t n, uint64_t m) {
  if (m <= 0) {
    return UINT64_C(1);
  } else {
    uint64_t m0 = m - 1;
    return (n * Nat::pow(n, m0));
  }
}
