#include <modulo_wrap.h>

unsigned int ModuloWrap::addr12_of_nat(const unsigned int &n) {
  return (4096u ? n % 4096u : n);
}

unsigned int ModuloWrap::byte_of_nat(const unsigned int &n) {
  return (256u ? n % 256u : n);
}

unsigned int ModuloWrap::nibble_of_nat(const unsigned int &n) {
  return (16u ? n % 16u : n);
}

unsigned int Nat::pow(const unsigned int &n, const unsigned int &m) {
  if (m <= 0) {
    return 1u;
  } else {
    unsigned int m0 = m - 1;
    return (n * Nat::pow(n, m0));
  }
}
