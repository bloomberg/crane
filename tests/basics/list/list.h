#ifndef INCLUDED_LIST
#define INCLUDED_LIST

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

  template <typename T1, MapsTo<T1, t_A, List<t_A>, T1> F1>
  T1 list_rect(const T1 f, F1 &&f0) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return f0(d_a0, *(d_a1), (*(d_a1)).template list_rect<T1>(f, f0));
    }
  }

  template <typename T1, MapsTo<T1, t_A, List<t_A>, T1> F1>
  T1 list_rec(const T1 f, F1 &&f0) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return f0(d_a0, *(d_a1), (*(d_a1)).template list_rec<T1>(f, f0));
    }
  }

  __attribute__((pure)) List<t_A> tl() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return List<t_A>::nil();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return *(d_a1);
    }
  }

  t_A hd(const t_A x) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return x;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return d_a0;
    }
  }

  t_A last(const t_A x) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return x;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return (*(d_a1)).last(d_a0);
    }
  }

  __attribute__((pure)) List<t_A> app(List<t_A> l2) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return l2;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return List<t_A>::cons(d_a0, (*(d_a1)).app(l2));
    }
  }

  template <typename T1, MapsTo<T1, t_A> F0>
  __attribute__((pure)) List<T1> map(F0 &&f) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return List<T1>::nil();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return List<T1>::cons(f(d_a0), (*(d_a1)).template map<T1>(f));
    }
  }

  static const List<unsigned int> &mytest() {
    static const List<unsigned int> v =
        List<unsigned int>::cons(
            3u,
            List<unsigned int>::cons(
                1u, List<unsigned int>::cons(2u, List<unsigned int>::nil())))
            .app(List<unsigned int>::cons(
                8u, List<unsigned int>::cons(
                        3u, List<unsigned int>::cons(
                                7u, List<unsigned int>::cons(
                                        9u, List<unsigned int>::nil())))));
    return v;
  }
};

#endif // INCLUDED_LIST
