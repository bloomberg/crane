#include "lowercase_eponymous_record.h"

LowercaseEponymousRecord::state::state0 LowercaseEponymousRecord::state::set_x(
    uint64_t n, const LowercaseEponymousRecord::state::state0 &s) {
  return state0{n, s.y};
}
