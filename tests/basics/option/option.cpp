#include <option.h>

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>

__attribute__((pure)) unsigned int
Option::get_or_default(const std::optional<unsigned int> o,
                       const unsigned int default0) {
  if (o.has_value()) {
    const unsigned int &x = *o;
    return x;
  } else {
    return default0;
  }
}

__attribute__((pure)) std::optional<unsigned int>
Option::safe_pred(const unsigned int n) {
  if (n <= 0) {
    return std::optional<unsigned int>();
  } else {
    unsigned int m = n - 1;
    return std::make_optional<unsigned int>(m);
  }
}

__attribute__((pure)) std::optional<unsigned int>
Option::chain_options(const std::optional<unsigned int> o1,
                      const std::optional<unsigned int> o2) {
  if (o1.has_value()) {
    const unsigned int &_x = *o1;
    return o1;
  } else {
    return o2;
  }
}
