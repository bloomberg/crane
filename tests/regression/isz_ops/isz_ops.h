#ifndef INCLUDED_ISZ_OPS
#define INCLUDED_ISZ_OPS

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

struct ListDef {
  template <typename T1>
  static T1 nth(uint64_t n, const List<T1> &l, T1 default0);
};

struct IszOps {
  static uint64_t nibble_of_nat(uint64_t n);

  struct state {
    List<uint64_t> regs;

    // ACCESSORS
    state clone() const { return state{this->regs}; }
  };

  static uint64_t get_reg(const state &s, uint64_t r);
  static uint64_t cycles_isz(const state &s, uint64_t r);
  static inline const uint64_t test_cycle_branch = cycles_isz(
      state{List<uint64_t>::cons(UINT64_C(15), List<uint64_t>::nil())},
      UINT64_C(0));
  static uint64_t isz_iterations(uint64_t v);
  static inline const uint64_t test_iterations_remaining =
      (isz_iterations(UINT64_C(0)) + isz_iterations(UINT64_C(12)));
  static bool isz_loops(const state &s, uint64_t r);
  static bool isz_terminates(const state &s, uint64_t r);
  static inline const uint64_t test_loop_flags = []() {
    return []() {
      state s = state{List<uint64_t>::cons(
          UINT64_C(15),
          List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()))};
      return ((isz_loops(s, UINT64_C(0)) ? UINT64_C(1) : UINT64_C(0)) +
              (isz_terminates(s, UINT64_C(0)) ? UINT64_C(1) : UINT64_C(0)));
    }();
  }();
  static inline const std::pair<std::pair<uint64_t, uint64_t>, uint64_t> t =
      std::make_pair(
          std::make_pair(test_cycle_branch, test_iterations_remaining),
          test_loop_flags);
};

template <typename T1>
T1 ListDef::nth(uint64_t n, const List<T1> &l, T1 default0) {
  if (n <= 0) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      return a0;
    }
  } else {
    uint64_t m = n - 1;
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a00, a10] = std::get<typename List<T1>::Cons>(l.v());
      return ListDef::template nth<T1>(m, *a10, default0);
    }
  }
}

#endif // INCLUDED_ISZ_OPS
