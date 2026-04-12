#include <monadic.h>

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) std::optional<unsigned int>
Monadic::safe_div(const unsigned int n, const unsigned int m) {
  if (m <= 0) {
    return std::optional<unsigned int>();
  } else {
    unsigned int m_ = m - 1;
    return std::make_optional<unsigned int>(((m_ + 1) ? n / (m_ + 1) : 0));
  }
}

__attribute__((pure)) std::optional<unsigned int>
Monadic::safe_sub(const unsigned int n, const unsigned int m) {
  if (n < m) {
    return std::optional<unsigned int>();
  } else {
    return std::make_optional<unsigned int>((((n - m) > n ? 0 : (n - m))));
  }
}

__attribute__((pure)) std::optional<unsigned int>
Monadic::div_then_sub(const unsigned int a, const unsigned int b,
                      const unsigned int c) {
  return option_bind<unsigned int, unsigned int>(
      safe_div(a, b), [=](const unsigned int x) mutable {
        return option_bind<unsigned int, unsigned int>(
            safe_sub(x, c), option_return<unsigned int>);
      });
}
