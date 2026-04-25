#ifndef INCLUDED_COIND_GUARD
#define INCLUDED_COIND_GUARD

#include "lazy.h"
#include <functional>
#include <memory>
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

template <typename T> struct is_shared_ptr : std::false_type {};

template <typename T>
struct is_shared_ptr<std::shared_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  return x ? std::make_unique<T>(x->clone()) : nullptr;
}

template <typename T>
std::shared_ptr<T> clone_value(const std::shared_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_shared<T>(x->clone()) : nullptr;
  } else {
    return x;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using TargetBare = std::remove_cvref_t<Target>;
  using SourceBare = std::remove_cvref_t<Source>;
  if constexpr (is_unique_ptr<TargetBare>::value) {
    using Inner = typename is_unique_ptr<TargetBare>::element_type;
    if constexpr (is_unique_ptr<SourceBare>::value) {
      using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires {
                             typename Inner::crane_element_type;
                             x->template clone_as<
                                 typename Inner::crane_element_type>();
                           }) {
        return std::make_unique<Inner>(
            x->template clone_as<typename Inner::crane_element_type>());
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_unique<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x.clone());
      }
    }
  } else if constexpr (is_shared_ptr<TargetBare>::value) {
    using Inner = typename is_shared_ptr<TargetBare>::element_type;
    if constexpr (is_shared_ptr<SourceBare>::value) {
      using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else if constexpr (is_unique_ptr<SourceBare>::value) {
      if (!x)
        return nullptr;
      if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_shared<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x.clone());
      }
    }
  } else if constexpr (std::is_same_v<TargetBare, SourceBare>) {
    return clone_value(x);
  } else if constexpr (is_unique_ptr<SourceBare>::value) {
    using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (is_shared_ptr<SourceBare>::value) {
    using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (requires {
                         typename TargetBare::crane_element_type;
                         x.template clone_as<
                             typename TargetBare::crane_element_type>();
                       }) {
    return x.template clone_as<typename TargetBare::crane_element_type>();
  } else if constexpr (requires { x.template clone_as<TargetBare>(); }) {
    return x.template clone_as<TargetBare>();
  } else {
    return Target(x);
  }
}

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;
  using crane_element_type = t_A;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  __attribute__((pure)) List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{clone_as_value<t_A>(d_a0),
                            clone_as_value<std::unique_ptr<List<t_A>>>(d_a1)});
    }
  }

  template <typename _CloneT0>
  __attribute__((pure)) List<_CloneT0> clone_as() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<_CloneT0>(typename List<_CloneT0>::Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<_CloneT0>(typename List<_CloneT0>::Cons{
          clone_as_value<_CloneT0>(d_a0),
          clone_as_value<std::unique_ptr<List<_CloneT0>>>(d_a1)});
    }
  }

  // CREATORS
  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1.clone())});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) List<t_A> *operator->() { return this; }

  __attribute__((pure)) const List<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = List<t_A>(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct CoindGuard {
  template <typename t_A> struct Stream {
    // TYPES
    struct Cons {
      t_A d_a0;
      std::shared_ptr<Stream<t_A>> d_a1;
    };

    using variant_t = std::variant<Cons>;

  private:
    // DATA
    crane::lazy<variant_t> d_lazyV_;

  public:
    // CREATORS
    explicit Stream(Cons _v)
        : d_lazyV_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit Stream(std::function<variant_t()> _thunk)
        : d_lazyV_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static std::shared_ptr<Stream<t_A>> cons(t_A a0,
                                             std::shared_ptr<Stream<t_A>> a1) {
      return std::make_shared<Stream<t_A>>(Cons{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<Stream<t_A>>
    lazy_(std::function<std::shared_ptr<Stream<t_A>>()> thunk) {
      return std::make_shared<Stream<t_A>>(
          std::function<variant_t()>([=]() mutable -> variant_t {
            std::shared_ptr<Stream<t_A>> _tmp = thunk();
            return _tmp->v();
          }));
    }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const {
      return d_lazyV_.force();
    }
  };

  template <typename T1> static T1 hd(const std::shared_ptr<Stream<T1>> &s) {
    const auto &[d_a0, d_a1] = std::get<typename Stream<T1>::Cons>(s->v());
    return d_a0;
  }

  template <typename T1>
  static std::shared_ptr<Stream<T1>> tl(const std::shared_ptr<Stream<T1>> &s) {
    const auto &[d_a0, d_a1] = std::get<typename Stream<T1>::Cons>(s->v());
    return Stream<T1>::lazy_(
        [=]() mutable -> std::shared_ptr<Stream<T1>> { return d_a1; });
  }

  template <typename T1, MapsTo<T1, T1> F0>
  static std::shared_ptr<Stream<T1>> iterate(F0 &&f, const T1 x) {
    return Stream<T1>::lazy_([=]() mutable -> std::shared_ptr<Stream<T1>> {
      return Stream<T1>::cons(x, iterate<T1>(f, f(x)));
    });
  }

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  static std::shared_ptr<Stream<T3>>
  zipWith(F0 &&f, const std::shared_ptr<Stream<T1>> &s1,
          const std::shared_ptr<Stream<T2>> &s2) {
    return Stream<T3>::lazy_([=]() mutable -> std::shared_ptr<Stream<T3>> {
      return Stream<T3>::cons(f(hd<T1>(s1), hd<T2>(s2)),
                              zipWith<T1, T2, T3>(f, tl<T1>(s1), tl<T2>(s2)));
    });
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static std::shared_ptr<Stream<T2>>
  smap(F0 &&f, const std::shared_ptr<Stream<T1>> &s) {
    return Stream<T2>::lazy_([=]() mutable -> std::shared_ptr<Stream<T2>> {
      return Stream<T2>::cons(f(hd<T1>(s)), smap<T1, T2>(f, tl<T1>(s)));
    });
  }

  template <typename T1, typename T2, MapsTo<std::pair<T1, T2>, T2> F0>
  static std::shared_ptr<Stream<T1>> unfold(F0 &&f, const T2 seed) {
    auto _cs = f(seed);
    const T1 &a = _cs.first;
    const T2 &s_ = _cs.second;
    return Stream<T1>::lazy_([=]() mutable -> std::shared_ptr<Stream<T1>> {
      return Stream<T1>::cons(a, unfold<T1, T2>(f, s_));
    });
  }

  template <typename T1>
  __attribute__((pure)) static List<T1>
  take(const unsigned int &n, const std::shared_ptr<Stream<T1>> &s) {
    if (n <= 0) {
      return List<T1>::nil();
    } else {
      unsigned int n_ = n - 1;
      return List<T1>::cons(hd<T1>(s), take<T1>(n_, tl<T1>(s)));
    }
  }

  static inline const std::shared_ptr<Stream<unsigned int>> nats =
      iterate<unsigned int>([](unsigned int x) { return (x + 1); }, 0u);
  static inline const std::shared_ptr<Stream<unsigned int>> evens =
      smap<unsigned int, unsigned int>(
          [](const unsigned int &n) { return (n * 2u); }, nats);
  static inline const std::shared_ptr<Stream<unsigned int>> fibs =
      unfold<unsigned int, std::pair<unsigned int, unsigned int>>(
          [](const std::pair<unsigned int, unsigned int> &pat) {
            const unsigned int &a = pat.first;
            const unsigned int &b = pat.second;
            return std::make_pair(a, std::make_pair(b, (a + b)));
          },
          std::make_pair(0u, 1u));
  static inline const std::shared_ptr<Stream<unsigned int>> sum_stream =
      zipWith<unsigned int, unsigned int, unsigned int>(
          [](unsigned int _x0, unsigned int _x1) -> unsigned int {
            return (_x0 + _x1);
          },
          nats, evens);
  static inline const List<unsigned int> test_nats_5 =
      take<unsigned int>(5u, nats);
  static inline const List<unsigned int> test_evens_5 =
      take<unsigned int>(5u, evens);
  static inline const List<unsigned int> test_fibs_8 =
      take<unsigned int>(8u, fibs);
  static inline const List<unsigned int> test_sum_5 =
      take<unsigned int>(5u, sum_stream);
  static inline const unsigned int test_iterate_hd = hd<unsigned int>(nats);
};

#endif // INCLUDED_COIND_GUARD
