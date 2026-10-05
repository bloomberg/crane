#include "page_address.h"

uint64_t PageAddress::addr12_of_nat(uint64_t n) {
  return (UINT64_C(4096) ? n % UINT64_C(4096) : n);
}

uint64_t PageAddress::page_of(uint64_t p) {
  return (UINT64_C(256) ? addr12_of_nat(p) / UINT64_C(256) : 0);
}

uint64_t PageAddress::page_base(uint64_t p) {
  return (page_of(p) * UINT64_C(256));
}

uint64_t PageAddress::branch_target(uint64_t pc, uint64_t off) {
  return (page_base(addr12_of_nat((pc + UINT64_C(2)))) +
          (UINT64_C(256) ? off % UINT64_C(256) : off));
}
