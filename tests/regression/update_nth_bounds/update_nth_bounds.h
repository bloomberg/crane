#ifndef INCLUDED_UPDATE_NTH_BOUNDS
#define INCLUDED_UPDATE_NTH_BOUNDS

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

  __attribute__((pure)) static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons{std::move(a0), std::make_unique<List<t_A>>(std::move(a1))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) List<t_A> skipn(const unsigned int &n) const {
    if (n <= 0) {
      return std::move(*(this));
    } else {
      unsigned int n0 = n - 1;
      auto &&_sv = *(this);
      if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v_mut())) {
        return List<t_A>::nil();
      } else {
        auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v_mut());
        return (*(d_a1)).skipn(n0);
      }
    }
  }

  __attribute__((pure)) List<t_A> firstn(const unsigned int &n) const {
    if (n <= 0) {
      return List<t_A>::nil();
    } else {
      unsigned int n0 = n - 1;
      auto &&_sv = *(this);
      if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
        return List<t_A>::nil();
      } else {
        const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
        return List<t_A>::cons(d_a0, (*(d_a1)).firstn(n0));
      }
    }
  }

  __attribute__((pure)) unsigned int length() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return ((*(d_a1)).length() + 1);
    }
  }

  __attribute__((pure)) List<t_A> app(List<t_A> m) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return m;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return List<t_A>::cons(d_a0, (*(d_a1)).app(std::move(m)));
    }
  }
};

struct UpdateNthBounds {
  template <typename T1>
  __attribute__((pure)) static List<T1> update_nth(unsigned int n, const T1 x,
                                                   List<T1> l) {
    if (n < l.length()) {
      return l.firstn(n).app(List<T1>::cons(x, l.skipn((n + 1))));
    } else {
      return l;
    }
  }

  static inline const unsigned int in_bounds_length =
      update_nth<unsigned int>(
          2u, 9u,
          List<unsigned int>::cons(
              1u, List<unsigned int>::cons(
                      2u, List<unsigned int>::cons(
                              3u, List<unsigned int>::cons(
                                      4u, List<unsigned int>::nil())))))
          .length();
  static inline const unsigned int out_of_bounds_length =
      update_nth<unsigned int>(
          9u, 7u,
          List<unsigned int>::cons(
              1u,
              List<unsigned int>::cons(
                  2u, List<unsigned int>::cons(3u, List<unsigned int>::nil()))))
          .length();
};

#endif // INCLUDED_UPDATE_NTH_BOUNDS
