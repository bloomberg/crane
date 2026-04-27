#ifndef INCLUDED_SPROP
#define INCLUDED_SPROP

#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct SPropTest {
  template <typename T1> static const T1 &sFalse_rect() {
    static const T1 v = []() { throw std::logic_error("absurd case"); }();
    return v;
  }

  template <typename T1> static const T1 &sFalse_rec() {
    static const T1 v = []() { throw std::logic_error("absurd case"); }();
    return v;
  }

  template <typename t_A> struct Box {
    t_A box_value;

    __attribute__((pure)) Box<t_A> *operator->() { return this; }

    __attribute__((pure)) const Box<t_A> *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) Box<t_A> clone() const {
      return Box<t_A>{[](auto &&__v) -> t_A {
        if constexpr (
            requires { __v ? 0 : 0; } && requires { *__v; } &&
            requires { __v->clone(); } && requires { __v.get(); }) {
          using _E = std::remove_cvref_t<decltype(*__v)>;
          return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
        } else if constexpr (requires { __v.clone(); }) {
          return __v.clone();
        } else {
          return __v;
        }
      }((*this).box_value)};
    }
  };

  __attribute__((pure)) static unsigned int guarded_pred(const unsigned int &n);
  __attribute__((pure)) static unsigned int safe_div(const unsigned int &_x0,
                                                     const unsigned int &_x1);
  static inline const unsigned int test_guarded = guarded_pred(5u);
  static inline const unsigned int test_box = 42u;
  static inline const unsigned int test_div = safe_div(10u, 3u);
};

#endif // INCLUDED_SPROP
