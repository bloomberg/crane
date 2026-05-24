#ifndef INCLUDED_STACK_OPS
#define INCLUDED_STACK_OPS

#include <any>
#include <memory>
#include <optional>
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

  uint64_t length() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return (a1->length() + 1);
    }
  }
};

struct StackOps {
  struct state_basic {
    List<uint64_t> stack_basic;

    // ACCESSORS
    state_basic clone() const { return state_basic{this->stack_basic}; }
  };

  struct state_with_acc {
    List<uint64_t> stack_with_acc;
    uint64_t acc;

    // ACCESSORS
    state_with_acc clone() const {
      return state_with_acc{this->stack_with_acc, this->acc};
    }
  };

  static std::pair<std::optional<uint64_t>, state_basic>
  pop_stack(state_basic s);
  static bool is_none(const std::optional<uint64_t> &o);
  static uint64_t option_or_zero(const std::optional<uint64_t> &o);
  static inline const bool empty_is_none =
      is_none(pop_stack(state_basic{List<uint64_t>::nil()}).first);
  static inline const uint64_t some_addr = option_or_zero(
      pop_stack(state_basic{List<uint64_t>::cons(
                    UINT64_C(9),
                    List<uint64_t>::cons(UINT64_C(8), List<uint64_t>::nil()))})
          .first);
  static std::pair<std::optional<uint64_t>, state_with_acc>
  pop_stack_acc(state_with_acc s);
  static inline const uint64_t pop_acc_test = []() -> uint64_t {
    auto _cs = pop_stack_acc(state_with_acc{
        List<uint64_t>::cons(
            UINT64_C(9),
            List<uint64_t>::cons(UINT64_C(8), List<uint64_t>::nil())),
        UINT64_C(3)});
    const std::optional<uint64_t> &o = _cs.first;
    const state_with_acc &s_ = _cs.second;
    if (o.has_value()) {
      const uint64_t &a = *o;
      return ((a + s_.stack_with_acc.length()) + s_.acc);
    } else {
      return s_.acc;
    }
  }();
  static state_basic push_stack(const state_basic &s, uint64_t addr);
  static uint64_t top_or_zero(const state_basic &s);
  static inline const uint64_t empty_len =
      push_stack(state_basic{List<uint64_t>::nil()}, UINT64_C(12))
          .stack_basic.length();
  static inline const uint64_t overflow_head = top_or_zero(push_stack(
      state_basic{List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(
              UINT64_C(2),
              List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil())))},
      UINT64_C(9)));
  static inline const uint64_t overflow_len =
      push_stack(
          state_basic{List<uint64_t>::cons(
              UINT64_C(1),
              List<uint64_t>::cons(
                  UINT64_C(2),
                  List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil())))},
          UINT64_C(9))
          .stack_basic.length();
  static state_basic push_stack_cap(const state_basic &s, uint64_t addr);
  static inline const uint64_t push_cap_test =
      push_stack_cap(state_basic{List<uint64_t>::cons(
                         UINT64_C(10),
                         List<uint64_t>::cons(
                             UINT64_C(20),
                             List<uint64_t>::cons(
                                 UINT64_C(30),
                                 List<uint64_t>::cons(
                                     UINT64_C(40), List<uint64_t>::nil()))))},
                     UINT64_C(7))
          .stack_basic.length();
  static inline const std::pair<
      std::pair<std::pair<std::pair<uint64_t, bool>, uint64_t>,
                std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>,
      uint64_t>
      t = std::make_pair(
          std::make_pair(
              std::make_pair(std::make_pair(some_addr, empty_is_none),
                             pop_acc_test),
              std::make_pair(std::make_pair(empty_len, overflow_head),
                             overflow_len)),
          push_cap_test);
};

#endif // INCLUDED_STACK_OPS
