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

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_unique<T>(x->clone()) : nullptr;
  } else {
    return x ? std::make_unique<T>(*x) : nullptr;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using T = std::remove_cvref_t<Target>;
  using S = std::remove_cvref_t<Source>;
  if constexpr (requires(const S &s) {
                  s.has_value();
                  *s;
                }) {
    if (!x.has_value())
      return T{};
    using TInner = std::remove_cvref_t<decltype(*std::declval<const T &>())>;
    return T{clone_as_value<TInner>(*x)};
  } else if constexpr (std::is_same_v<T, S>) {
    if constexpr (is_unique_ptr<T>::value) {
      return clone_value(x);
    } else if constexpr (requires { x.clone(); }) {
      return x.clone();
    } else {
      return x;
    }
  } else if constexpr (is_unique_ptr<S>::value) {
    if (!x)
      return T{};
    return clone_as_value<T>(*x);
  } else if constexpr (is_unique_ptr<T>::value) {
    using Inner = typename is_unique_ptr<T>::element_type;
    return std::make_unique<Inner>(clone_as_value<Inner>(x));
  } else {
    return T(x);
  }
}

enum class Bool0 { e_TRUE0, e_FALSE0 };

template <typename t_A> struct Sig {
  // TYPES
  struct Exist {
    t_A d_x;
  };

  using variant_t = std::variant<Exist>;
  using crane_element_type = t_A;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Sig() {}

  explicit Sig(Exist _v) : d_v_(std::move(_v)) {}

  Sig(const Sig<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Sig(Sig<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  __attribute__((pure)) Sig<t_A> &operator=(const Sig<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) Sig<t_A> &operator=(Sig<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) Sig<t_A> clone() const {
    auto &&_sv = *(this);
    const auto &[d_x] = std::get<Exist>(_sv.v());
    return Sig<t_A>(Exist{clone_value(d_x)});
  }

  // CREATORS
  template <typename _U> explicit Sig(const Sig<_U> &_other) {
    const auto &[d_x] = std::get<typename Sig<_U>::Exist>(_other.v());
    d_v_ = Exist{clone_as_value<t_A>(d_x)};
  }

  __attribute__((pure)) static Sig<t_A> exist(t_A x) {
    return Sig(Exist{std::move(x)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) Sig<t_A> *operator->() { return this; }

  __attribute__((pure)) const Sig<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = Sig<t_A>(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct RocqBug10757 {
  template <typename T1, MapsTo<Bool0, T1, T1> F0, MapsTo<T1, T1> F1>
  __attribute__((pure)) static Sig<T1>
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
        const auto &[d_x] = std::get<typename Sig<T1>::Exist>(y.v());
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
  __attribute__((pure)) static Sig<T1> iterate(F0 &&beq, F1 &&f, const T1 x) {
    return iterate_func(beq, f, Sig<T1>::exist(x));
  }
};

#endif // INCLUDED_ROCQ_BUG_10757
