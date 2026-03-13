#ifndef INCLUDED_SPROP
#define INCLUDED_SPROP

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct Nat {
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  divmod(const unsigned int x, const unsigned int y, const unsigned int q,
         const unsigned int u);
  __attribute__((pure)) static unsigned int div(const unsigned int x,
                                                const unsigned int y);
};

struct SPropTest {
  template <typename T1> static const T1 &sFalse_rect() {
    static const T1 v = [](void) { throw std::logic_error("absurd case"); }();
    return v;
  }

  template <typename T1> static const T1 &sFalse_rec() {
    static const T1 v = [](void) { throw std::logic_error("absurd case"); }();
    return v;
  }

  template <typename t_A> struct Box {
    t_A box_value;
  };

  __attribute__((pure)) static unsigned int guarded_pred(const unsigned int n);
  __attribute__((pure)) static unsigned int safe_div(const unsigned int _x0,
                                                     const unsigned int _x1);
  static inline const unsigned int test_guarded = guarded_pred(5u);
  static inline const unsigned int test_box = 42u;
  static inline const unsigned int test_div = safe_div(10u, 3u);
};

#endif // INCLUDED_SPROP
