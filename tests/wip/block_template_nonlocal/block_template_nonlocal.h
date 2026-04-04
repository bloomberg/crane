#ifndef INCLUDED_BLOCK_TEMPLATE_NONLOCAL
#define INCLUDED_BLOCK_TEMPLATE_NONLOCAL

#include <iostream>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct BlockTemplateNonlocal {
  /// Block template in pure let binding — compiled to static inline initializer
  /// with an expression-position IIFE.
  /// Generates: static inline const unsigned int x = (&() -> unsigned int { ...
  /// }() + 42u); Bug: & is invalid in non-local lambda. Should be ().
  static inline const unsigned int pure_block_let = ([&]() -> unsigned int {
    unsigned int _r;
    std::cin >> _r;
    return _r;
  }() + 42u);
  /// Two pure block templates in same expression
  static inline const unsigned int two_pure_blocks = ([&]() -> unsigned int {
    unsigned int _r;
    std::cin >> _r;
    return _r;
  }() + [&]() -> unsigned int {
    unsigned int _r;
    std::cin >> _r;
    return _r;
  }());
};

#endif // INCLUDED_BLOCK_TEMPLATE_NONLOCAL
