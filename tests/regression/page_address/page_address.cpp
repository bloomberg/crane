#include <page_address.h>

#include <type_traits>
#include <utility>

__attribute__((pure)) unsigned int
PageAddress::addr12_of_nat(const unsigned int n) {
  return (n % 4096u);
}

__attribute__((pure)) unsigned int PageAddress::page_of(const unsigned int p) {
  return (256u ? addr12_of_nat(p) / 256u : 0);
}

__attribute__((pure)) unsigned int
PageAddress::page_base(const unsigned int p) {
  return (page_of(p) * 256u);
}

__attribute__((pure)) unsigned int
PageAddress::branch_target(const unsigned int pc, const unsigned int off) {
  return (page_base(addr12_of_nat((pc + 2u))) + (off % 256u));
}
