#include <pstring.h>

#include <memory>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) std::string
PString::nat_to_string(const std::shared_ptr<Nat> &n) {
  if (std::holds_alternative<typename Nat::O>(n->v())) {
    return "O";
  } else {
    const auto &_m = *std::get_if<typename Nat::S>(&n->v());
    return "S"s + nat_to_string(_m.d_a0);
  }
}

__attribute__((pure)) int PString::nat_to_int(const std::shared_ptr<Nat> &n) {
  if (std::holds_alternative<typename Nat::O>(n->v())) {
    return 0;
  } else {
    const auto &_m = *std::get_if<typename Nat::S>(&n->v());
    return 1 + nat_to_int(_m.d_a0);
  }
}
