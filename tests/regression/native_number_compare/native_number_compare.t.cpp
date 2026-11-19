#include <cassert>
#include <cstdint>
#include <native_number_compare.h>

using M = NativeNumberCompare;

int main() {
  const uint64_t big = UINT64_C(1) << 40;
  assert(M::nat_cmp(3, 5) == 0);
  assert(M::nat_cmp(5, 5) == 1);
  assert(M::nat_cmp(5, 3) == 2);
  assert(M::nat_cmp(big, big + 1) == 0);
  assert(M::nat_cmp(big, big) == 1);
  assert(M::nat_cmp(big + 1, big) == 2);
  assert(M::nat_cmp_value(big + 1, big) == 2);
  assert(M::nat_cmp_value(0, big) == 0);
  assert(M::nat_cmp_(big, big + 1) == 0);
  assert(M::nat_cmp_(big, big) == 1);
  assert(M::nat_dec(big, big));
  assert(!M::nat_dec(big, big + 1));
  assert(M::nat_dec(0, 0));

  const unsigned int nbig = 4000000000u;
  assert(M::n_cmp(0u, 1u) == 0);
  assert(M::n_cmp(nbig, nbig) == 1);
  assert(M::n_cmp(nbig + 1u, nbig) == 2);
  assert(M::n_dec(nbig, nbig));
  assert(!M::n_dec(nbig, nbig - 1u));

  assert(M::pos_cmp(1u, nbig) == 0);
  assert(M::pos_cmp(nbig, nbig) == 1);
  assert(M::pos_cmp(nbig, 1u) == 2);
  assert(M::pos_dec(nbig, nbig));
  assert(!M::pos_dec(nbig, 1u));

  const int64_t zbig = INT64_C(1) << 50;
  assert(M::z_cmp(-zbig, zbig) == 0);
  assert(M::z_cmp(-zbig, -zbig) == 1);
  assert(M::z_cmp(zbig, -zbig) == 2);
  assert(M::z_cmp(-1, 0) == 0);
  assert(M::z_dec(-zbig, -zbig));
  assert(!M::z_dec(zbig, -zbig));
  return 0;
}
