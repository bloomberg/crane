#ifndef INCLUDED_PROGRAM_TARGETS_REGION_SCAN
#define INCLUDED_PROGRAM_TARGETS_REGION_SCAN

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;

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

  template <typename _U> List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{[&]() -> A {
                        if constexpr (std::is_same_v<_U, std::any>) {
                          return crane_any_cast<A>(a);
                        } else {
                          return A(a);
                        }
                      }(),
                      (l ? std::make_shared<List<A>>(*l) : nullptr)};
    }
  }

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    crane::small_vector<std::shared_ptr<List<A>>> _stack = {};
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
        std::atomic_thread_fence(std::memory_order_acquire);
        _drain(_cur->v_mut());
      }
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, A &>
  bool forallb(F0 &&f) const {
    const List<A> *_self = this;

    /// _Enter: captures varying parameters for each recursive call.
    struct _Enter {
      const List<A> *_self;
    };

    /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
    struct _Resume_Cons {
      std::decay_t<decltype(std::declval<F0 &>()(std::declval<A &>()))> a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    bool _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{_self});
    /// Loopified forallb: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = true;
        } else {
          const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_Resume_Cons{f(a0)});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = (_f.a0 && std::move(_result));
      }
    }
    return _result;
  }
};

struct ProgramTargetsRegionScan {
  struct instruction {
    // TYPES
    struct JUN {
      uint64_t a0;
    };

    struct JMS {
      uint64_t a0;
    };

    struct NOP {};

    using variant_t = std::variant<JUN, JMS, NOP>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    instruction() {}

    explicit instruction(JUN _v) : v_(std::move(_v)) {}

    explicit instruction(JMS _v) : v_(std::move(_v)) {}

    explicit instruction(NOP _v) : v_(_v) {}

    static instruction jun(uint64_t a0) { return instruction(JUN{a0}); }

    static instruction jms(uint64_t a0) { return instruction(JMS{a0}); }

    static instruction nop() { return instruction(NOP{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, uint64_t &>
  static T1 instruction_rect(F0 &&f, F1 &&f0, T1 f1, const instruction &i) {
    if (std::holds_alternative<typename instruction::JUN>(i.v())) {
      const auto &[a0] = std::get<typename instruction::JUN>(i.v());
      return f(a0);
    } else if (std::holds_alternative<typename instruction::JMS>(i.v())) {
      const auto &[a0] = std::get<typename instruction::JMS>(i.v());
      return f0(a0);
    } else {
      return f1;
    }
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, uint64_t &>
  static T1 instruction_rec(F0 &&f, F1 &&f0, T1 f1, const instruction &i) {
    if (std::holds_alternative<typename instruction::JUN>(i.v())) {
      const auto &[a0] = std::get<typename instruction::JUN>(i.v());
      return f(a0);
    } else if (std::holds_alternative<typename instruction::JMS>(i.v())) {
      const auto &[a0] = std::get<typename instruction::JMS>(i.v());
      return f0(a0);
    } else {
      return f1;
    }
  }

  struct layout {
    uint64_t base_addr;
    uint64_t code_size;
  };

  static std::optional<uint64_t> jump_target(const instruction &i);
  static bool addr_in_regionb(uint64_t addr, const layout &l);
  static bool target_in_layoutb(const layout &l, const instruction &i);
  static bool program_targets_okb(const List<instruction> &prog,
                                  const layout &l);
  static inline const uint64_t t = []() {
    layout l = layout{UINT64_C(200), UINT64_C(20)};
    List<instruction> p = List<instruction>::cons(
        instruction::nop(),
        List<instruction>::cons(
            instruction::jun(UINT64_C(205)),
            List<instruction>::cons(instruction::jms(UINT64_C(218)),
                                    List<instruction>::nil())));
    if (program_targets_okb(std::move(p), std::move(l))) {
      return UINT64_C(1);
    } else {
      return UINT64_C(0);
    }
  }();
};

#endif // INCLUDED_PROGRAM_TARGETS_REGION_SCAN
