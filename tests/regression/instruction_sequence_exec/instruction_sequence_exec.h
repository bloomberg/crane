#ifndef INCLUDED_INSTRUCTION_SEQUENCE_EXEC
#define INCLUDED_INSTRUCTION_SEQUENCE_EXEC

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

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

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  List clone() const {
    List _out{};

    struct _CloneFrame {
      const List *_src;
      List *_dst;
    };

    std::vector<_CloneFrame> _stack;
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List *_src = _frame._src;
      List *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        const auto &_alt = std::get<Nil>(_src->v());
        _dst->d_v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->d_v_ =
            Cons{_alt.d_a0, _alt.d_a1 ? std::make_unique<List>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->d_v_);
        if (_alt.d_a1)
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  static List<t_A> nil() { return List(Nil{}); }

  static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons{std::move(a0), std::make_unique<List<t_A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List>> _stack;
    auto _drain = [&](List &_node) {
      if (std::holds_alternative<Cons>(_node.d_v_)) {
        auto &_alt = std::get<Cons>(_node.d_v_);
        if (_alt.d_a1)
          _stack.push_back(std::move(_alt.d_a1));
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node)
        _drain(*_node);
    }
  }

  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }
};

struct InstructionSequenceExec {
  struct state {
    unsigned int pc_;
    unsigned int acc_;

    // ACCESSORS
    state clone() const { return state{(*(this)).pc_, (*(this)).acc_}; }
  };

  struct instruction {
    // TYPES
    struct NOP_ {};

    struct INC_PC {};

    struct ADD_ACC {
      unsigned int d_a0;
    };

    using variant_t = std::variant<NOP_, INC_PC, ADD_ACC>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    instruction() {}

    explicit instruction(NOP_ _v) : d_v_(_v) {}

    explicit instruction(INC_PC _v) : d_v_(_v) {}

    explicit instruction(ADD_ACC _v) : d_v_(std::move(_v)) {}

    instruction(const instruction &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    instruction(instruction &&_other) : d_v_(std::move(_other.d_v_)) {}

    instruction &operator=(const instruction &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    instruction &operator=(instruction &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    instruction clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<NOP_>(_sv.v())) {
        return instruction(NOP_{});
      } else if (std::holds_alternative<INC_PC>(_sv.v())) {
        return instruction(INC_PC{});
      } else {
        const auto &[d_a0] = std::get<ADD_ACC>(_sv.v());
        return instruction(ADD_ACC{d_a0});
      }
    }

    // CREATORS
    static instruction nop_() { return instruction(NOP_{}); }

    static instruction inc_pc() { return instruction(INC_PC{}); }

    static instruction add_acc(unsigned int a0) {
      return instruction(ADD_ACC{std::move(a0)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F2>
  static T1 instruction_rect(const T1 f, const T1 f0, F2 &&f1,
                             const instruction &i) {
    if (std::holds_alternative<typename instruction::NOP_>(i.v())) {
      return f;
    } else if (std::holds_alternative<typename instruction::INC_PC>(i.v())) {
      return f0;
    } else {
      const auto &[d_a0] = std::get<typename instruction::ADD_ACC>(i.v());
      return f1(d_a0);
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F2>
  static T1 instruction_rec(const T1 f, const T1 f0, F2 &&f1,
                            const instruction &i) {
    if (std::holds_alternative<typename instruction::NOP_>(i.v())) {
      return f;
    } else if (std::holds_alternative<typename instruction::INC_PC>(i.v())) {
      return f0;
    } else {
      const auto &[d_a0] = std::get<typename instruction::ADD_ACC>(i.v());
      return f1(d_a0);
    }
  }

  static state execute(state s, const instruction &i);
  static state exec_program(const List<instruction> &prog, state s);
  static inline const state sample = state{0u, 1u};
  static inline const unsigned int t = []() {
    state s_ = exec_program(
        List<instruction>::cons(
            instruction::inc_pc(),
            List<instruction>::cons(
                instruction::add_acc(2u),
                List<instruction>::cons(instruction::inc_pc(),
                                        List<instruction>::nil()))),
        sample);
    return (s_.pc_ + s_.acc_);
  }();
};

#endif // INCLUDED_INSTRUCTION_SEQUENCE_EXEC
