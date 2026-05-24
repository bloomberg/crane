#ifndef INCLUDED_PARTIAL_APPLY
#define INCLUDED_PARTIAL_APPLY

#include <any>
#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
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

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &, A &>
  T1 fold_left(F0 &&f, T1 a0) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return a0;
    } else {
      const auto &[a1, a2] = std::get<typename List<A>::Cons>(this->v());
      return a2->template fold_left<T1>(f, f(a0, a1));
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, A &>
  List<T1> map(F0 &&f) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return List<T1>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return List<T1>::cons(f(a0), a1->template map<T1>(f));
    }
  }
};

struct PartialApply {
  static List<uint64_t> inc_all(const List<uint64_t> &l);
  static List<std::pair<uint64_t, uint64_t>> tag_all(const List<uint64_t> &l);
  static List<std::optional<uint64_t>> wrap_all(const List<uint64_t> &l);
  static List<std::function<List<uint64_t>(List<uint64_t>)>>
  prepend_each(const List<uint64_t> &l);

  template <typename A> struct tagged {
    // DATA
    uint64_t a0;
    A a1;

    // ACCESSORS
    tagged<A> clone() const { return {a0, a1}; }

    // CREATORS
    static tagged<A> tag(uint64_t a0, A a1) { return {a0, std::move(a1)}; }
  };

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, uint64_t &, T1 &>
  static T2 tagged_rect(F0 &&f, const tagged<T1> &t) {
    const auto &[a0, a1] = t;
    return f(a0, a1);
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, uint64_t &, T1 &>
  static T2 tagged_rec(F0 &&f, const tagged<T1> &t) {
    const auto &[a0, a1] = t;
    return f(a0, a1);
  }

  static List<tagged<bool>> tag_with(uint64_t n, const List<bool> &l);
  static List<std::pair<uint64_t, std::pair<uint64_t, uint64_t>>>
  double_tag(const List<uint64_t> &l);
  static uint64_t sum_with_init(uint64_t init, const List<uint64_t> &l);
  static inline const List<uint64_t> test_inc = inc_all(List<uint64_t>::cons(
      UINT64_C(1), List<uint64_t>::cons(
                       UINT64_C(2), List<uint64_t>::cons(
                                        UINT64_C(3), List<uint64_t>::nil()))));
  static inline const List<std::pair<uint64_t, uint64_t>> test_tag =
      tag_all(List<uint64_t>::cons(
          UINT64_C(10),
          List<uint64_t>::cons(
              UINT64_C(20),
              List<uint64_t>::cons(UINT64_C(30), List<uint64_t>::nil()))));
  static inline const List<std::optional<uint64_t>> test_wrap =
      wrap_all(List<uint64_t>::cons(
          UINT64_C(5),
          List<uint64_t>::cons(
              UINT64_C(6),
              List<uint64_t>::cons(UINT64_C(7), List<uint64_t>::nil()))));
  static inline const List<tagged<bool>> test_tag_with = tag_with(
      UINT64_C(99),
      List<bool>::cons(
          true,
          List<bool>::cons(false, List<bool>::cons(true, List<bool>::nil()))));
  static inline const uint64_t test_sum = sum_with_init(
      UINT64_C(100),
      List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(
              UINT64_C(2),
              List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()))));
};

#endif // INCLUDED_PARTIAL_APPLY
