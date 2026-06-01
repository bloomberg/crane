#ifndef INCLUDED_LET_FIX_NESTED_CLONE
#define INCLUDED_LET_FIX_NESTED_CLONE

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

template <typename T1>
uint64_t _count_nested_outer(const List<List<T1>> xss, const uint64_t acc) {
  if (std::holds_alternative<typename List<List<T1>>::Nil>(xss.v())) {
    return acc;
  } else {
    const auto &[a0, a1] = std::get<typename List<List<T1>>::Cons>(xss.v());
    auto inner_impl = [](auto &_self_inner, const List<T1> &ys,
                         uint64_t n) -> uint64_t {
      if (std::holds_alternative<typename List<T1>::Nil>(ys.v())) {
        return n;
      } else {
        const auto &[a00, a10] = std::get<typename List<T1>::Cons>(ys.v());
        return _self_inner(_self_inner, *a10, (UINT64_C(1) + n));
      }
    };
    auto inner = [&](const List<T1> &ys, uint64_t n) -> uint64_t {
      return inner_impl(inner_impl, ys, n);
    };
    return _count_nested_outer<T1>(*a1, (inner(a0, UINT64_C(0)) + acc));
  }
}

struct LetFixNestedClone {
  static uint64_t sum_nested(const List<List<uint64_t>> &ll);
  static uint64_t count_nested(const List<List<uint64_t>> &ll);
  static inline const uint64_t test_sum = sum_nested(List<List<uint64_t>>::cons(
      List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(UINT64_C(2), List<uint64_t>::nil())),
      List<List<uint64_t>>::cons(
          List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()),
          List<List<uint64_t>>::cons(
              List<uint64_t>::cons(
                  UINT64_C(4),
                  List<uint64_t>::cons(
                      UINT64_C(5), List<uint64_t>::cons(
                                       UINT64_C(6), List<uint64_t>::nil()))),
              List<List<uint64_t>>::nil()))));

  static inline const uint64_t test_count =
      count_nested(List<List<uint64_t>>::cons(
          List<uint64_t>::cons(
              UINT64_C(1),
              List<uint64_t>::cons(UINT64_C(2), List<uint64_t>::nil())),
          List<List<uint64_t>>::cons(
              List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()),
              List<List<uint64_t>>::cons(
                  List<uint64_t>::cons(
                      UINT64_C(4),
                      List<uint64_t>::cons(
                          UINT64_C(5),
                          List<uint64_t>::cons(UINT64_C(6),
                                               List<uint64_t>::nil()))),
                  List<List<uint64_t>>::nil()))));
};

#endif // INCLUDED_LET_FIX_NESTED_CLONE
