#ifndef INCLUDED_PROGRAM_WF_PROP
#define INCLUDED_PROGRAM_WF_PROP

#include <memory>
#include <optional>
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

struct ProgramWfProp {
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
      if (std::holds_alternative<JUN>(this->v())) {
        const auto &[a0] = std::get<JUN>(this->v());
        return instruction(JUN{a0});
      } else if (std::holds_alternative<JMS>(this->v())) {
        const auto &[a0] = std::get<JMS>(this->v());
        return instruction(JMS{a0});
      } else {
        return instruction(NOP{});
      }
    }

    // CREATORS
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

    // ACCESSORS
    layout clone() const {
      return layout{(*this).base_addr, (*this).code_size};
    }
  };

  static std::optional<uint64_t> jump_target(const instruction &i);
  static inline const layout sample_layout =
      layout{UINT64_C(200), UINT64_C(20)};
  static inline const List<instruction> sample_prog = List<instruction>::cons(
      instruction::nop(),
      List<instruction>::cons(
          instruction::jun(UINT64_C(205)),
          List<instruction>::cons(instruction::jms(UINT64_C(218)),
                                  List<instruction>::nil())));
};

#endif // INCLUDED_PROGRAM_WF_PROP
