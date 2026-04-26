#ifndef INCLUDED_ROCQ_BUG_11114
#define INCLUDED_ROCQ_BUG_11114

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
      return List<t_A>(Cons{clone_value(d_a0), clone_value(d_a1)});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ = Cons{clone_as_value<t_A>(d_a0),
                  d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1)});
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

struct RocqBug11114 {
  struct t {
    // TYPES
    struct T0 {
      unsigned int d_k;
    };

    using variant_t = std::variant<T0>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    t() {}

    explicit t(T0 _v) : d_v_(std::move(_v)) {}

    t(const t &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    t(t &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) t &operator=(const t &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) t &operator=(t &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) t clone() const {
      auto &&_sv = *(this);
      const auto &[d_k] = std::get<T0>(_sv.v());
      return t(T0{d_k});
    }

    // CREATORS
    __attribute__((pure)) static t t0(unsigned int k) {
      return t(T0{std::move(k)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) t *operator->() { return this; }

    __attribute__((pure)) const t *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = t(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 t_rect(const List<unsigned int> &, F1 &&f, const t &t0) {
    const auto &[d_k] = std::get<typename t::T0>(t0.v());
    return f(d_k);
  }

  template <typename T1, MapsTo<T1, unsigned int> F1>
  static T1 t_rec(const List<unsigned int> &, F1 &&f, const t &t0) {
    const auto &[d_k] = std::get<typename t::T0>(t0.v());
    return f(d_k);
  }

  struct pkg {
    List<unsigned int> _sig;
    t _t;

    __attribute__((pure)) pkg *operator->() { return this; }

    __attribute__((pure)) const pkg *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) pkg clone() const {
      return pkg{(*(this))._sig, (*(this))._t};
    }
  };

  template <MapsTo<unsigned int, unsigned int> F0>
  __attribute__((pure)) static pkg map(F0 &&f, const pkg &p) {
    return pkg{p._sig, [=]() mutable {
                 auto &&_sv = p._t;
                 const auto &[d_k] = std::get<typename t::T0>(_sv.v());
                 return t::t0(f(d_k));
               }()};
  }

  static inline const pkg test_pkg =
      pkg{List<unsigned int>::cons(1u, List<unsigned int>::nil()), t::t0(2u)};
  static inline const pkg test_map =
      map([](const unsigned int &x) { return (x + 1u); }, test_pkg);
};

#endif // INCLUDED_ROCQ_BUG_11114
