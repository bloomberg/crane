#ifndef INCLUDED_EXTRACT_DIRECTIVES
#define INCLUDED_EXTRACT_DIRECTIVES

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

struct ExtractDirectives {
  __attribute__((pure)) static unsigned int offset(const unsigned int base,
                                                   const unsigned int x);
  __attribute__((pure)) static unsigned int scale(const unsigned int base,
                                                  const unsigned int x);
  __attribute__((pure)) static unsigned int transform(const unsigned int base,
                                                      const unsigned int x);
  __attribute__((pure)) static unsigned int safe_pred(const unsigned int n);
  static inline const unsigned int test_offset = offset(10u, 5u);
  static inline const unsigned int test_scale = scale(3u, 4u);
  static inline const unsigned int test_transform = transform(2u, 3u);
  static inline const unsigned int test_safe_pred = safe_pred(5u);
  __attribute__((pure)) static unsigned int inner_add(const unsigned int _x0,
                                                      const unsigned int _x1);
  __attribute__((pure)) static unsigned int inner_mul(const unsigned int _x0,
                                                      const unsigned int _x1);
  __attribute__((pure)) static unsigned int outer_use(const unsigned int a,
                                                      const unsigned int b);
  static inline const unsigned int test_inner = inner_add(3u, 7u);
  static inline const unsigned int test_outer = outer_use(4u, 5u);
};

#endif // INCLUDED_EXTRACT_DIRECTIVES
