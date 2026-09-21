#ifndef INCLUDED_ROCQ_BUG_10757
#define INCLUDED_ROCQ_BUG_10757

#include "crane_fn.h"
#include <any>
#include <functional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

enum class Bool0;
template <typename A> struct Sig;
enum class Bool0 { TRUE_, FALSE_ };

template <typename A> struct Sig {
  // DATA
  A x;

  // ACCESSORS
  Sig<A> clone() const { return {x}; }

  template <typename _U> operator Sig<_U>() const {
    return {[&]() -> _U {
      if constexpr (crane_convertible<_U, const A &>) {
        return crane_convert<_U>(x);
      } else {
        throw std::logic_error(
            "unreachable: inactive constructor field at this instantiation");
      }
    }()};
  }

  // CREATORS
  static Sig<A> exist(A x) { return {std::move(x)}; }
};

struct RocqBug10757 {
  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<Bool0, F0 &, T1 &, T1 &> &&
             std::is_invocable_r_v<T1, F1 &, T1 &>
  static Sig<T1>
  iterate_func(F0 &&beq, F1 &&f,
               const T1 &x) { // Precondition: (exists _ : le x (F x), forall z
                              // : A, le (F z) z -> le x z)
    T1 x0 = [&]() {
      const auto &[x1] = x;
      return x1;
    }();
    std::function<Sig<T1>(T1)> iterate0 = [=](T1 x1) mutable {
      Sig<T1> y = Sig<T1>::exist(Sig<T1>::exist(x1));
      return iterate_func<T1>(beq, f, [=]() mutable {
        auto &[x2] = y;
        return x2;
      }());
    };
    T1 x_ = f(x0);
    Bool0 filtered_var = beq(x0, x_);
    switch (filtered_var) {
    case Bool0::TRUE_: {
      return Sig<T1>::exist(std::move(x0));
    }
    case Bool0::FALSE_: {
      return iterate0(std::move(x_));
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<Bool0, F0 &, T1 &, T1 &> &&
             std::is_invocable_r_v<T1, F1 &, T1 &>
  static Sig<T1> iterate(F0 &&beq, F1 &&f, T1 x) {
    return iterate_func(beq, f, Sig<T1>::exist(std::move(x)));
  }
};

#endif // INCLUDED_ROCQ_BUG_10757
