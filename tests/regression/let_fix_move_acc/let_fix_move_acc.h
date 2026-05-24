#ifndef INCLUDED_LET_FIX_MOVE_ACC
#define INCLUDED_LET_FIX_MOVE_ACC

#include <any>
#include <memory>
#include <utility>
#include <variant>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct LetFixMoveAcc {
  template <typename T1> static List<T1> reverse_list(const List<T1> &l) {
    auto go_impl = [](auto &_self_go, const List<T1> &xs,
                      List<T1> acc) -> List<T1> {
      if (std::holds_alternative<typename List<T1>::Nil>(xs.v())) {
        return acc;
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(xs.v());
        return _self_go(_self_go, *a1, List<T1>::cons(a0, std::move(acc)));
      }
    };
    auto go = [&](const List<T1> &xs, List<T1> acc) -> List<T1> {
      return go_impl(go_impl, xs, acc);
    };
    return go(l, List<T1>::nil());
  }

  template <typename T1> static List<T1> snoc(const List<T1> &l, T1 x) {
    auto rev_impl = [](auto &_self_rev, const List<T1> &xs,
                       List<T1> acc) -> List<T1> {
      if (std::holds_alternative<typename List<T1>::Nil>(xs.v())) {
        return acc;
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(xs.v());
        return _self_rev(_self_rev, *a1, List<T1>::cons(a0, std::move(acc)));
      }
    };
    auto rev = [&](const List<T1> &xs, List<T1> acc) -> List<T1> {
      return rev_impl(rev_impl, xs, acc);
    };
    return rev(rev(l, List<T1>::nil()), List<T1>::cons(x, List<T1>::nil()));
  }

  static inline const List<uint64_t> test_rev =
      reverse_list<uint64_t>(List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(
              UINT64_C(2),
              List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()))));
  static inline const List<uint64_t> test_snoc = snoc<uint64_t>(
      List<uint64_t>::cons(
          UINT64_C(10),
          List<uint64_t>::cons(UINT64_C(20), List<uint64_t>::nil())),
      UINT64_C(30));
};

#endif // INCLUDED_LET_FIX_MOVE_ACC
