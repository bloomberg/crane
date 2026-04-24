#include <pstring.h>

#include <memory>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) std::string PString::nat_to_string(const Nat &n) {
  if (std::holds_alternative<typename Nat::O>(n.v())) {
    return "O";
  } else {
    const auto &[d_a0] = std::get<typename Nat::S>(n.v());
    return "S"s + nat_to_string(*(d_a0));
  }
}

__attribute__((pure)) int PString::nat_to_int(const Nat &n) {
  if (std::holds_alternative<typename Nat::O>(n.v())) {
    return 0;
  } else {
    const auto &[d_a0] = std::get<typename Nat::S>(n.v());
    return 1 + nat_to_int(*(d_a0));
  }
}
