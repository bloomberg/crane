#ifndef INCLUDED_IDENTIFIER_ESCAPE_PARAM
#define INCLUDED_IDENTIFIER_ESCAPE_PARAM

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct IdentifierEscapeParam {
  __attribute__((pure)) static unsigned int
  id_from_param(const unsigned int double0);
  __attribute__((pure)) static unsigned int
  add_one_from_param(const unsigned int double0);
  static inline const unsigned int t = add_one_from_param(6u);
};

#endif // INCLUDED_IDENTIFIER_ESCAPE_PARAM
