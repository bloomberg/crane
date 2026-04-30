#ifndef INCLUDED_ROCQ_BUG_10757
#define INCLUDED_ROCQ_BUG_10757

#include <cassert>
#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

enum class Bool0 { e_TRUE0, e_FALSE0 };

template <typename t_A> struct Sig {
  // TYPES
  struct Exist {
    t_A d_x;
  };

  using variant_t = std::variant<Exist>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Sig() {}

  explicit Sig(Exist _v) : d_v_(std::move(_v)) {}

  Sig(const Sig<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Sig(Sig<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  Sig<t_A> &operator=(const Sig<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  Sig<t_A> &operator=(Sig<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  Sig<t_A> clone() const {
    auto &&_sv = *(this);
    const auto &[d_x] = std::get<Exist>(_sv.v());
    return Sig<t_A>(Exist{d_x});
  }

  // CREATORS
  template <typename _U> explicit Sig(const Sig<_U> &_other) {
    const auto &[d_x] = std::get<typename Sig<_U>::Exist>(_other.v());
    d_v_ = Exist{t_A(d_x)};
  }

  static Sig<t_A> exist(t_A x) { return Sig(Exist{std::move(x)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }
};

struct RocqBug10757 {
  template <typename T1, MapsTo<Bool0, T1, T1> F0, MapsTo<T1, T1> F1>
  static Sig<T1>
  iterate_func(F0 &&beq, F1 &&f,
               const T1 x) { // Precondition: (exists _ : le x (F x), forall z :
                             // A, le (F z) z -> le x z)
    assert(true);
    T1 x0 = [&]() {
      const auto &[d_x] = std::get<typename Sig<T1>::Exist>(x.v());
      return d_x;
    }();
    std::function<Sig<T1>(T1)> iterate0 = [=](const T1 x1) mutable {
      Sig<T1> y = Sig<Sig<T1>>::exist(Sig<T1>::exist(x1));
      return iterate_func<T1>(beq, f, [=]() mutable {
        auto &[d_x] = std::get<typename Sig<T1>::Exist>(y.v_mut());
        return d_x;
      }());
    };
    T1 x_ = f(x0);
    Bool0 filtered_var = beq(x0, x_);
    switch (filtered_var) {
    case Bool0::e_TRUE0: {
      return Sig<T1>::exist(x0);
    }
    case Bool0::e_FALSE0: {
      return iterate0(x_);
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1, MapsTo<Bool0, T1, T1> F0, MapsTo<T1, T1> F1>
  static Sig<T1> iterate(F0 &&beq, F1 &&f, const T1 x) {
    return iterate_func(beq, f, Sig<T1>::exist(x));
  }
};

#endif // INCLUDED_ROCQ_BUG_10757
