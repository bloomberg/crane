#ifndef INCLUDED_STEP_FETCH_DECODE_EXEC
#define INCLUDED_STEP_FETCH_DECODE_EXEC

#include <any>
#include <memory>
#include <type_traits>
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
};

struct ListDef {
  template <typename T1>
  static T1 nth(uint64_t n, const List<T1> &l, T1 default0);
};

struct StepFetchDecodeExec {
  struct instruction {
    // TYPES
    struct NOP {};

    struct ADD_ACC {
      uint64_t a0;
    };

    using variant_t = std::variant<NOP, ADD_ACC>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    instruction() {}

    explicit instruction(NOP _v) : v_(_v) {}

    explicit instruction(ADD_ACC _v) : v_(std::move(_v)) {}

    static instruction nop() { return instruction(NOP{}); }

    static instruction add_acc(uint64_t a0) { return instruction(ADD_ACC{a0}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &>
  static T1 instruction_rect(T1 f, F1 &&f0, const instruction &i) {
    if (std::holds_alternative<typename instruction::NOP>(i.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename instruction::ADD_ACC>(i.v());
      return f0(a0);
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &>
  static T1 instruction_rec(T1 f, F1 &&f0, const instruction &i) {
    if (std::holds_alternative<typename instruction::NOP>(i.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename instruction::ADD_ACC>(i.v());
      return f0(a0);
    }
  }

  struct state {
    uint64_t acc;
    uint64_t pc;
    List<uint64_t> rom;
  };

  static uint64_t fetch_byte(const state &s, uint64_t addr);
  static instruction decode(uint64_t b1, uint64_t b2);
  static state execute(const state &s, const instruction &i);
  static state step(const state &s);
  static inline const uint64_t t = []() {
    state s1 = step(state{
        UINT64_C(3), UINT64_C(0),
        List<uint64_t>::cons(
            UINT64_C(1),
            List<uint64_t>::cons(
                UINT64_C(6),
                List<uint64_t>::cons(UINT64_C(0), List<uint64_t>::nil())))});
    return (s1.acc + s1.pc);
  }();
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

#endif // INCLUDED_STEP_FETCH_DECODE_EXEC
