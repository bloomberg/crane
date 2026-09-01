#include "tc_carrier_option_cast.h"

uint64_t TcCarrierOptionCast::test(uint64_t n) {
  return OptBox::peek(crane_erase_fn(OptBox::wrap(n)));
}
