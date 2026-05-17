#include "page_address.h"

unsigned int PageAddress::addr12_of_nat(unsigned int n) {
  return (4096u ? n % 4096u : n);
}

unsigned int PageAddress::page_of(unsigned int p) {
  return (256u ? addr12_of_nat(p) / 256u : 0);
}

unsigned int PageAddress::page_base(unsigned int p) {
  return (page_of(p) * 256u);
}

unsigned int PageAddress::branch_target(unsigned int pc, unsigned int off) {
  return (page_base(addr12_of_nat((pc + 2u))) + (256u ? off % 256u : off));
}
