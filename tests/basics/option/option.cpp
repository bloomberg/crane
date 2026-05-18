#include "option.h"

uint64_t Option::get_or_default(const std::optional<uint64_t> &o,
                                uint64_t default0) {
  if (o.has_value()) {
    const uint64_t &x = *o;
    return x;
  } else {
    return default0;
  }
}

std::optional<uint64_t> Option::safe_pred(uint64_t n) {
  if (n <= 0) {
    return std::optional<uint64_t>();
  } else {
    uint64_t m = n - 1;
    return std::make_optional<uint64_t>(m);
  }
}

std::optional<uint64_t> Option::chain_options(std::optional<uint64_t> o1,
                                              std::optional<uint64_t> o2) {
  if (o1.has_value()) {
    const uint64_t &_x = *o1;
    return o1;
  } else {
    return o2;
  }
}
