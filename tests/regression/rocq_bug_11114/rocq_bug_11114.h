#ifndef INCLUDED_ROCQ_BUG_11114
#define INCLUDED_ROCQ_BUG_11114

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

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

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
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
      return List<t_A>(Cons{
          d_a0, d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

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

    t &operator=(const t &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    t &operator=(t &&_other) {
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
    inline variant_t &v_mut() { return d_v_; }

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
      return pkg{(*(this))._sig.clone(), (*(this))._t.clone()};
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
