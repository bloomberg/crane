#ifndef INCLUDED_INSTRUCTION_SEQUENCE_EXEC
#define INCLUDED_INSTRUCTION_SEQUENCE_EXEC

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
    std::unique_ptr<List<A>> l;
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

  List(const List<A> &_other) : v_(std::move(_other.clone().v_)) {}

  List(List<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  List<A> clone() const {
    List<A> _out{};

    struct _CloneFrame {
      const List<A> *_src;
      List<A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<A> *_src = _frame._src;
      List<A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->v_ = Cons{_alt.a, _alt.l ? std::make_unique<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.l) {
          _stack.push_back({_alt.l.get(), _dst_alt.l.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a), l ? std::make_unique<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_unique<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
        if (_alt.l) {
          _stack.push_back(std::move(_alt.l));
        }
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node) {
        _drain(*_node);
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct InstructionSequenceExec {
  struct state {
    uint64_t pc_;
    uint64_t acc_;

    // ACCESSORS
    state clone() const { return state{this->pc_, this->acc_}; }
  };

  struct instruction {
    // TYPES
    struct NOP_ {};

    struct INC_PC {};

    struct ADD_ACC {
      uint64_t a0;
    };

    using variant_t = std::variant<NOP_, INC_PC, ADD_ACC>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    instruction() {}

    explicit instruction(NOP_ _v) : v_(_v) {}

    explicit instruction(INC_PC _v) : v_(_v) {}

    explicit instruction(ADD_ACC _v) : v_(std::move(_v)) {}

    instruction(const instruction &_other) : v_(std::move(_other.clone().v_)) {}

    instruction(instruction &&_other) noexcept : v_(std::move(_other.v_)) {}

    instruction &operator=(const instruction &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    instruction &operator=(instruction &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    instruction clone() const {
      if (std::holds_alternative<NOP_>(this->v())) {
        return instruction(NOP_{});
      } else if (std::holds_alternative<INC_PC>(this->v())) {
        return instruction(INC_PC{});
      } else {
        const auto &[a0] = std::get<ADD_ACC>(this->v());
        return instruction(ADD_ACC{a0});
      }
    }

    // CREATORS
    static instruction nop_() { return instruction(NOP_{}); }

    static instruction inc_pc() { return instruction(INC_PC{}); }

    static instruction add_acc(uint64_t a0) { return instruction(ADD_ACC{a0}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F2>
    requires std::is_invocable_r_v<T1, F2 &, uint64_t &>
  static T1 instruction_rect(T1 f, T1 f0, F2 &&f1, const instruction &i) {
    if (std::holds_alternative<typename instruction::NOP_>(i.v())) {
      return f;
    } else if (std::holds_alternative<typename instruction::INC_PC>(i.v())) {
      return f0;
    } else {
      const auto &[a0] = std::get<typename instruction::ADD_ACC>(i.v());
      return f1(a0);
    }
  }

  template <typename T1, typename F2>
    requires std::is_invocable_r_v<T1, F2 &, uint64_t &>
  static T1 instruction_rec(T1 f, T1 f0, F2 &&f1, const instruction &i) {
    if (std::holds_alternative<typename instruction::NOP_>(i.v())) {
      return f;
    } else if (std::holds_alternative<typename instruction::INC_PC>(i.v())) {
      return f0;
    } else {
      const auto &[a0] = std::get<typename instruction::ADD_ACC>(i.v());
      return f1(a0);
    }
  }

  static state execute(state s, const instruction &i);
  static state exec_program(const List<instruction> &prog, state s);
  static inline const state sample = state{UINT64_C(0), UINT64_C(1)};
  static inline const uint64_t t = []() {
    state s_ = exec_program(
        List<instruction>::cons(
            instruction::inc_pc(),
            List<instruction>::cons(
                instruction::add_acc(UINT64_C(2)),
                List<instruction>::cons(instruction::inc_pc(),
                                        List<instruction>::nil()))),
        sample);
    return (s_.pc_ + s_.acc_);
  }();
};

#endif // INCLUDED_INSTRUCTION_SEQUENCE_EXEC
