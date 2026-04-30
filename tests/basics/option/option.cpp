#include <option.h>

unsigned int Option::get_or_default(const std::optional<unsigned int> &o,
                                    unsigned int default0) {
  if (o.has_value()) {
    const unsigned int &x = *o;
    return x;
  } else {
    return default0;
  }
}

std::optional<unsigned int> Option::safe_pred(const unsigned int &n) {
  if (n <= 0) {
    return std::optional<unsigned int>();
  } else {
    unsigned int m = n - 1;
    return std::make_optional<unsigned int>(m);
  }
}

std::optional<unsigned int>
Option::chain_options(std::optional<unsigned int> o1,
                      std::optional<unsigned int> o2) {
  if (o1.has_value()) {
    const unsigned int &_x = *o1;
    return o1;
  } else {
    return o2;
  }
}
