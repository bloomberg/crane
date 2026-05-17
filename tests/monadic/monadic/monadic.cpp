#include "monadic.h"

std::optional<unsigned int> Monadic::safe_div(unsigned int n, unsigned int m) {
  if (m <= 0) {
    return std::optional<unsigned int>();
  } else {
    unsigned int m_ = m - 1;
    return std::make_optional<unsigned int>(((m_ + 1) ? n / (m_ + 1) : 0));
  }
}

std::optional<unsigned int> Monadic::safe_sub(unsigned int n, unsigned int m) {
  if (n < m) {
    return std::optional<unsigned int>();
  } else {
    return std::make_optional<unsigned int>((((n - m) > n ? 0 : (n - m))));
  }
}

std::optional<unsigned int>
Monadic::div_then_sub(unsigned int a, unsigned int b, unsigned int c) {
  return option_bind<unsigned int, unsigned int>(
      safe_div(a, b), [=](unsigned int x) mutable {
        return option_bind<unsigned int, unsigned int>(
            safe_sub(x, c), option_return<unsigned int>);
      });
}
