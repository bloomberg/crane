#ifndef INCLUDED_PROGRAM_WF_PROP
#define INCLUDED_PROGRAM_WF_PROP

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
  List<t_A> clone() const {
    List<t_A> _out{};

    struct _CloneFrame {
      const List<t_A> *_src;
      List<t_A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<t_A> *_src = _frame._src;
      List<t_A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->d_v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->d_v_ = Cons{_alt.d_a0,
                          _alt.d_a1 ? std::make_unique<List<t_A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->d_v_);
        if (_alt.d_a1) {
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        }
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
    std::vector<std::unique_ptr<List<t_A>>> _stack{};
    auto _drain = [&](List<t_A> &_node) {
      if (std::holds_alternative<Cons>(_node.d_v_)) {
        auto &_alt = std::get<Cons>(_node.d_v_);
        if (_alt.d_a1) {
          _stack.push_back(std::move(_alt.d_a1));
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

  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }
};

struct ProgramWfProp {
  struct instruction {
    // TYPES
    struct JUN {
      unsigned int d_a0;
    };

    struct JMS {
      unsigned int d_a0;
    };

    struct NOP {};

    using variant_t = std::variant<JUN, JMS, NOP>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    instruction() {}

    explicit instruction(JUN _v) : d_v_(std::move(_v)) {}

    explicit instruction(JMS _v) : d_v_(std::move(_v)) {}

    explicit instruction(NOP _v) : d_v_(_v) {}

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
      if (std::holds_alternative<JUN>(_sv.v())) {
        const auto &[d_a0] = std::get<JUN>(_sv.v());
        return instruction(JUN{d_a0});
      } else if (std::holds_alternative<JMS>(_sv.v())) {
        const auto &[d_a0] = std::get<JMS>(_sv.v());
        return instruction(JMS{d_a0});
      } else {
        return instruction(NOP{});
      }
    }

    // CREATORS
    static instruction jun(unsigned int a0) {
      return instruction(JUN{std::move(a0)});
    }

    static instruction jms(unsigned int a0) {
      return instruction(JMS{std::move(a0)});
    }

    static instruction nop() { return instruction(NOP{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 instruction_rect(F0 &&f, F1 &&f0, const T1 f1,
                             const instruction &i) {
    if (std::holds_alternative<typename instruction::JUN>(i.v())) {
      const auto &[d_a0] = std::get<typename instruction::JUN>(i.v());
      return f(d_a0);
    } else if (std::holds_alternative<typename instruction::JMS>(i.v())) {
      const auto &[d_a0] = std::get<typename instruction::JMS>(i.v());
      return f0(d_a0);
    } else {
      return f1;
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1>
  static T1 instruction_rec(F0 &&f, F1 &&f0, const T1 f1,
                            const instruction &i) {
    if (std::holds_alternative<typename instruction::JUN>(i.v())) {
      const auto &[d_a0] = std::get<typename instruction::JUN>(i.v());
      return f(d_a0);
    } else if (std::holds_alternative<typename instruction::JMS>(i.v())) {
      const auto &[d_a0] = std::get<typename instruction::JMS>(i.v());
      return f0(d_a0);
    } else {
      return f1;
    }
  }

  struct layout {
    unsigned int base_addr;
    unsigned int code_size;

    // ACCESSORS
    layout clone() const {
      return layout{(*(this)).base_addr, (*(this)).code_size};
    }
  };

  static std::optional<unsigned int> jump_target(const instruction &i);
  static inline const layout sample_layout = layout{200u, 20u};
  static inline const List<instruction> sample_prog = List<instruction>::cons(
      instruction::nop(),
      List<instruction>::cons(
          instruction::jun(205u),
          List<instruction>::cons(instruction::jms(218u),
                                  List<instruction>::nil())));
};

#endif // INCLUDED_PROGRAM_WF_PROP
