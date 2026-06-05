#ifndef INCLUDED_RESET_STATE
#define INCLUDED_RESET_STATE

#include <any>
#include <memory>
#include <utility>
#include <variant>
#include <vector>

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
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        _drain(_cur->v_mut());
      }
    }
  }

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

struct ListDef {
  template <typename T1>
  static T1 nth(uint64_t n, const List<T1> &l, T1 default0);
};

struct ResetState {
  struct state_full {
    uint64_t acc;
    List<uint64_t> regs_full;
    bool carry;
    uint64_t pc_full;
    List<uint64_t> stack;
    List<uint64_t> ram_sys;
    List<uint64_t> rom;
  };

  struct state_minimal {
    List<uint64_t> regs_minimal;
    bool carry_minimal;
    uint64_t pc_minimal;
    List<uint64_t> ram_sys_minimal;
    List<uint64_t> rom_minimal;
  };

  static state_full reset_state_full(const state_full &s);
  static inline const uint64_t memory_preserve_test = []() {
    state_full s = state_full{
        UINT64_C(9),
        List<uint64_t>::cons(
            UINT64_C(1),
            List<uint64_t>::cons(UINT64_C(2), List<uint64_t>::nil())),
        true,
        UINT64_C(55),
        List<uint64_t>::cons(
            UINT64_C(8),
            List<uint64_t>::cons(UINT64_C(7), List<uint64_t>::nil())),
        List<uint64_t>::cons(
            UINT64_C(3),
            List<uint64_t>::cons(
                UINT64_C(4),
                List<uint64_t>::cons(UINT64_C(5), List<uint64_t>::nil()))),
        List<uint64_t>::cons(
            UINT64_C(10),
            List<uint64_t>::cons(UINT64_C(11), List<uint64_t>::nil()))};
    state_full s_ = reset_state_full(std::move(s));
    return (
        ((s_.acc + ListDef::template nth<uint64_t>(UINT64_C(1), s_.ram_sys,
                                                   UINT64_C(0))) +
         ListDef::template nth<uint64_t>(UINT64_C(0), s_.rom, UINT64_C(0))) +
        s_.stack.length());
  }();
  static state_minimal reset_state_minimal(const state_minimal &s);
  static inline const uint64_t pc_clear_test =
      reset_state_minimal(
          state_minimal{
              List<uint64_t>::cons(
                  UINT64_C(1),
                  List<uint64_t>::cons(UINT64_C(2), List<uint64_t>::nil())),
              true, UINT64_C(99),
              List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()),
              List<uint64_t>::cons(
                  UINT64_C(4),
                  List<uint64_t>::cons(UINT64_C(5), List<uint64_t>::nil()))})
          .pc_minimal;
  static inline const std::pair<uint64_t, uint64_t> t =
      std::make_pair(memory_preserve_test, pc_clear_test);
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

#endif // INCLUDED_RESET_STATE
