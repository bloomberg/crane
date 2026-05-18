#include "monadic.h"

std::optional<uint64_t> Monadic::safe_div(uint64_t n, uint64_t m) {
  if (m <= 0) {
    return std::optional<uint64_t>();
  } else {
    uint64_t m_ = m - 1;
    return std::make_optional<uint64_t>(((m_ + 1) ? n / (m_ + 1) : 0));
  }
}

std::optional<uint64_t> Monadic::safe_sub(uint64_t n, uint64_t m) {
  if (n < m) {
    return std::optional<uint64_t>();
  } else {
    return std::make_optional<uint64_t>((((n - m) > n ? 0 : (n - m))));
  }
}

std::optional<uint64_t> Monadic::div_then_sub(uint64_t a, uint64_t b,
                                              uint64_t c) {
  return option_bind<uint64_t, uint64_t>(
      safe_div(a, b), [=](uint64_t x) mutable {
        return option_bind<uint64_t, uint64_t>(safe_sub(x, c),
                                               option_return<uint64_t>);
      });
}
