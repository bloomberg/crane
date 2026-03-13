#ifndef INCLUDED_KEYWORD_CLASS_GLOBAL
#define INCLUDED_KEYWORD_CLASS_GLOBAL

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

struct KeywordClassGlobal {
  __attribute__((pure)) static unsigned int class_(const unsigned int n);
  static inline const unsigned int t = class_(4u);
};

#endif // INCLUDED_KEYWORD_CLASS_GLOBAL
