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

struct OptionTupleWrapperSafe {
  enum class tag { SomeTag, NoneTag };

  template <typename T1>
  static T1 tag_rect(const T1 f, const T1 f0, const tag t) {
    return [&](void) {
      switch (t) {
      case tag::SomeTag: {
        return f;
      }
      case tag::NoneTag: {
        return f0;
      }
      }
    }();
  }

  template <typename T1>
  static T1 tag_rec(const T1 f, const T1 f0, const tag t) {
    return [&](void) {
      switch (t) {
      case tag::SomeTag: {
        return f;
      }
      case tag::NoneTag: {
        return f0;
      }
      }
    }();
  }

  static unsigned int pick_nat(const bool b);

  static inline const unsigned int t = pick_nat(true);
};
