#ifndef INCLUDED_TAIL_REC_ZIP
#define INCLUDED_TAIL_REC_ZIP

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A, typename t_B> struct Prod {
  // TYPES
  struct Pair {
    t_A d_a0;
    t_B d_a1;
  };

  using variant_t = std::variant<Pair>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Prod() {}

  explicit Prod(Pair _v) : d_v_(std::move(_v)) {}

  Prod(const Prod<t_A, t_B> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Prod(Prod<t_A, t_B> &&_other) : d_v_(std::move(_other.d_v_)) {}

  __attribute__((pure)) Prod<t_A, t_B> &
  operator=(const Prod<t_A, t_B> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) Prod<t_A, t_B> &operator=(Prod<t_A, t_B> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) Prod<t_A, t_B> clone() const {
    auto &&_sv = *(this);
    const auto &[d_a0, d_a1] = std::get<Pair>(_sv.v());
    t_A __c0;
    if constexpr (
        requires { d_a0 ? 0 : 0; } && requires { *d_a0; } &&
        requires { d_a0->clone(); } && requires { d_a0.get(); }) {
      using _E = std::remove_cvref_t<decltype(*d_a0)>;
      __c0 = d_a0 ? std::make_unique<_E>(d_a0->clone()) : nullptr;
    } else if constexpr (requires { d_a0.clone(); }) {
      __c0 = d_a0.clone();
    } else {
      __c0 = d_a0;
    }
    t_B __c1;
    if constexpr (
        requires { d_a1 ? 0 : 0; } && requires { *d_a1; } &&
        requires { d_a1->clone(); } && requires { d_a1.get(); }) {
      using _E = std::remove_cvref_t<decltype(*d_a1)>;
      __c1 = d_a1 ? std::make_unique<_E>(d_a1->clone()) : nullptr;
    } else if constexpr (requires { d_a1.clone(); }) {
      __c1 = d_a1.clone();
    } else {
      __c1 = d_a1;
    }
    return Prod<t_A, t_B>(Pair{std::move(__c0), std::move(__c1)});
  }

  // CREATORS
  template <typename _U0, typename _U1>
  explicit Prod(const Prod<_U0, _U1> &_other) {
    const auto &[d_a0, d_a1] =
        std::get<typename Prod<_U0, _U1>::Pair>(_other.v());
    d_v_ = Pair{
        [&]<typename _DstT = t_A>(auto &&__v) -> _DstT {
          if constexpr (
              requires { *__v; } && !requires { std::declval<_DstT>().get(); })
            return _DstT(*__v);
          else if constexpr (
              !requires { *__v; } &&
              requires { std::declval<_DstT>().get(); }) {
            using _E =
                std::remove_pointer_t<decltype(std::declval<_DstT>().get())>;
            return std::make_unique<_E>(std::move(__v));
          } else
            return _DstT(__v);
        }(d_a0),
        [&]<typename _DstT = t_B>(auto &&__v) -> _DstT {
          if constexpr (
              requires { *__v; } && !requires { std::declval<_DstT>().get(); })
            return _DstT(*__v);
          else if constexpr (
              !requires { *__v; } &&
              requires { std::declval<_DstT>().get(); }) {
            using _E =
                std::remove_pointer_t<decltype(std::declval<_DstT>().get())>;
            return std::make_unique<_E>(std::move(__v));
          } else
            return _DstT(__v);
        }(d_a1)};
  }

  __attribute__((pure)) static Prod<t_A, t_B> pair(t_A a0, t_B a1) {
    return Prod(Pair{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) Prod<t_A, t_B> *operator->() { return this; }

  __attribute__((pure)) const Prod<t_A, t_B> *operator->() const {
    return this;
  }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = Prod<t_A, t_B>(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

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
      t_A __c0;
      if constexpr (
          requires { d_a0 ? 0 : 0; } && requires { *d_a0; } &&
          requires { d_a0->clone(); } && requires { d_a0.get(); }) {
        using _E = std::remove_cvref_t<decltype(*d_a0)>;
        __c0 = d_a0 ? std::make_unique<_E>(d_a0->clone()) : nullptr;
      } else if constexpr (requires { d_a0.clone(); }) {
        __c0 = d_a0.clone();
      } else {
        __c0 = d_a0;
      }
      return List<t_A>(
          Cons{std::move(__c0),
               d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ = Cons{
          [&]<typename _DstT = t_A>(auto &&__v) -> _DstT {
            if constexpr (
                requires { *__v; } &&
                !requires { std::declval<_DstT>().get(); })
              return _DstT(*__v);
            else if constexpr (
                !requires { *__v; } &&
                requires { std::declval<_DstT>().get(); }) {
              using _E =
                  std::remove_pointer_t<decltype(std::declval<_DstT>().get())>;
              return std::make_unique<_E>(std::move(__v));
            } else
              return _DstT(__v);
          }(d_a0),
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

  __attribute__((pure)) List<t_A> rev() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return List<t_A>::nil();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return (*(d_a1)).rev().app(List<t_A>::cons(d_a0, List<t_A>::nil()));
    }
  }

  __attribute__((pure)) List<t_A> app(List<t_A> m) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return m;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return List<t_A>::cons(d_a0, (*(d_a1)).app(m));
    }
  }
};

template <typename T1, typename T2>
__attribute__((pure)) List<Prod<T1, T2>> better_zip(const List<T1> &la,
                                                    const List<T2> &lb) {
  std::function<List<Prod<T1, T2>>(List<T1>, List<T2>, List<Prod<T1, T2>>)> go;
  go = [&](List<T1> la0, List<T2> lb0,
           List<Prod<T1, T2>> acc) -> List<Prod<T1, T2>> {
    if (std::holds_alternative<typename List<T1>::Nil>(la0.v())) {
      return acc.rev();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(la0.v());
      if (std::holds_alternative<typename List<T2>::Nil>(lb0.v())) {
        return acc.rev();
      } else {
        const auto &[d_a00, d_a10] = std::get<typename List<T2>::Cons>(lb0.v());
        return go(
            *(d_a1), *(d_a10),
            List<Prod<T1, T2>>::cons(Prod<T1, T2>::pair(d_a0, d_a00), acc));
      }
    }
  };
  return go(la, lb, List<Prod<T1, T2>>::nil());
}

#endif // INCLUDED_TAIL_REC_ZIP
