#ifndef INCLUDED_ROCQ_BUG_10757
#define INCLUDED_ROCQ_BUG_10757

#include <cassert>
#include <functional>
#include <type_traits>
#include <utility>
#include <variant>

enum class Bool0 { TRUE_, FALSE_ };

template <typename A> struct Sig {
  // TYPES
  struct Exist {
    A x;
  };

  using variant_t = std::variant<Exist>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Sig() {}

  explicit Sig(Exist _v) : v_(std::move(_v)) {}

  Sig(const Sig<A> &_other) : v_(std::move(_other.clone().v_)) {}

  Sig(Sig<A> &&_other) : v_(std::move(_other.v_)) {}

  Sig<A> &operator=(const Sig<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  Sig<A> &operator=(Sig<A> &&_other) {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  Sig<A> clone() const {
    const auto &[x] = std::get<Exist>(this->v());
    return Sig<A>(Exist{x});
  }

  // CREATORS
  template <typename _U> explicit Sig(const Sig<_U> &_other) {
    const auto &[x] = std::get<typename Sig<_U>::Exist>(_other.v());
    this->v_ = Exist{A(x)};
  }

  static Sig<A> exist(A x) { return Sig(Exist{std::move(x)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct RocqBug10757 {
  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<Bool0, F0 &, T1 &, T1 &> &&
             std::is_invocable_r_v<T1, F1 &, T1 &>
  static Sig<T1>
  iterate_func(F0 &&beq, F1 &&f,
               const T1 &x) { // Precondition: (exists _ : le x (F x), forall z
                              // : A, le (F z) z -> le x z)
    assert(true);
    T1 x0 = [&]() {
      const auto &[x0] = std::get<typename Sig<T1>::Exist>(x.v());
      return x0;
    }();
    std::function<Sig<T1>(T1)> iterate0 = [=](T1 x1) mutable {
      Sig<T1> y = Sig<Sig<T1>>::exist(Sig<T1>::exist(x1));
      return iterate_func<T1>(beq, f, [=]() mutable {
        auto &[x2] = std::get<typename Sig<T1>::Exist>(y.v_mut());
        return x2;
      }());
    };
    T1 x_ = f(x0);
    Bool0 filtered_var = beq(x0, x_);
    switch (filtered_var) {
    case Bool0::TRUE_: {
      return Sig<T1>::exist(x0);
    }
    case Bool0::FALSE_: {
      return iterate0(x_);
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<Bool0, F0 &, T1 &, T1 &> &&
             std::is_invocable_r_v<T1, F1 &, T1 &>
  static Sig<T1> iterate(F0 &&beq, F1 &&f, T1 x) {
    return iterate_func(beq, f, Sig<T1>::exist(x));
  }
};

#endif // INCLUDED_ROCQ_BUG_10757
