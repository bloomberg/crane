#ifndef INCLUDED_DISASSEMBLE_OPS
#define INCLUDED_DISASSEMBLE_OPS

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
    A a0;
    std::unique_ptr<List<A>> a1;
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

  List(List<A> &&_other) : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) {
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
        _dst->v_ =
            Cons{_alt.a0, _alt.a1 ? std::make_unique<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.a1) {
          _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
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
      const auto &[a0, a1] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a0), a1 ? std::make_unique<List<A>>(*a1) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a0, List<A> a1) {
    return List(Cons{std::move(a0), std::make_unique<List<A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
        if (_alt.a1) {
          _stack.push_back(std::move(_alt.a1));
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

  unsigned int length() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return 0u;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return ((*a1).length() + 1);
    }
  }
};

struct ListDef {
  template <typename T1> static List<T1> repeat(T1 x, unsigned int n);
};

struct DisassembleOps {
  struct instruction {
    // TYPES
    struct NOP {};

    struct NOP2 {};

    struct LDM {
      unsigned int a0;
    };

    struct LDM2 {
      unsigned int a0;
    };

    using variant_t = std::variant<NOP, NOP2, LDM, LDM2>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    instruction() {}

    explicit instruction(NOP _v) : v_(_v) {}

    explicit instruction(NOP2 _v) : v_(_v) {}

    explicit instruction(LDM _v) : v_(std::move(_v)) {}

    explicit instruction(LDM2 _v) : v_(std::move(_v)) {}

    instruction(const instruction &_other) : v_(std::move(_other.clone().v_)) {}

    instruction(instruction &&_other) : v_(std::move(_other.v_)) {}

    instruction &operator=(const instruction &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    instruction &operator=(instruction &&_other) {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    instruction clone() const {
      if (std::holds_alternative<NOP>(this->v())) {
        return instruction(NOP{});
      } else if (std::holds_alternative<NOP2>(this->v())) {
        return instruction(NOP2{});
      } else if (std::holds_alternative<LDM>(this->v())) {
        const auto &[a0] = std::get<LDM>(this->v());
        return instruction(LDM{a0});
      } else {
        const auto &[a0] = std::get<LDM2>(this->v());
        return instruction(LDM2{a0});
      }
    }

    // CREATORS
    static instruction nop() { return instruction(NOP{}); }

    static instruction nop2() { return instruction(NOP2{}); }

    static instruction ldm(unsigned int a0) { return instruction(LDM{a0}); }

    static instruction ldm2(unsigned int a0) { return instruction(LDM2{a0}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F2, typename F3>
    requires std::is_invocable_r_v<T1, F2 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F3 &, unsigned int &>
  static T1 instruction_rect(T1 f, T1 f0, F2 &&f1, F3 &&f2,
                             const instruction &i) {
    if (std::holds_alternative<typename instruction::NOP>(i.v())) {
      return f;
    } else if (std::holds_alternative<typename instruction::NOP2>(i.v())) {
      return f0;
    } else if (std::holds_alternative<typename instruction::LDM>(i.v())) {
      const auto &[a0] = std::get<typename instruction::LDM>(i.v());
      return f1(a0);
    } else {
      const auto &[a0] = std::get<typename instruction::LDM2>(i.v());
      return f2(a0);
    }
  }

  template <typename T1, typename F2, typename F3>
    requires std::is_invocable_r_v<T1, F2 &, unsigned int &> &&
             std::is_invocable_r_v<T1, F3 &, unsigned int &>
  static T1 instruction_rec(T1 f, T1 f0, F2 &&f1, F3 &&f2,
                            const instruction &i) {
    if (std::holds_alternative<typename instruction::NOP>(i.v())) {
      return f;
    } else if (std::holds_alternative<typename instruction::NOP2>(i.v())) {
      return f0;
    } else if (std::holds_alternative<typename instruction::LDM>(i.v())) {
      const auto &[a0] = std::get<typename instruction::LDM>(i.v());
      return f1(a0);
    } else {
      const auto &[a0] = std::get<typename instruction::LDM2>(i.v());
      return f2(a0);
    }
  }

  static instruction decode1(unsigned int b1, unsigned int b2);
  static List<unsigned int> drop_(unsigned int n, List<unsigned int> l);
  static std::optional<std::pair<instruction, unsigned int>>
  disassemble1(const List<unsigned int> &rom0, unsigned int addr);
  static inline const unsigned int test_disassemble_drop_window =
      []() -> unsigned int {
    auto _cs = disassemble1(
        List<unsigned int>::cons(
            1u, List<unsigned int>::cons(
                    2u, List<unsigned int>::cons(
                            3u, List<unsigned int>::cons(
                                    4u, List<unsigned int>::cons(
                                            5u, List<unsigned int>::nil()))))),
        1u);
    if (_cs.has_value()) {
      const std::pair<instruction, unsigned int> &p = *_cs;
      const instruction &_x = p.first;
      const unsigned int &next = p.second;
      return next;
    } else {
      return 0u;
    }
  }();
  static instruction decode2(unsigned int b1, unsigned int b2);

  template <typename T1> static List<T1> drop(unsigned int n, List<T1> l) {
    if (n <= 0) {
      return l;
    } else {
      unsigned int n_ = n - 1;
      if (std::holds_alternative<typename List<T1>::Nil>(l.v_mut())) {
        return List<T1>::nil();
      } else {
        auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v_mut());
        return drop<T1>(n_, *a1);
      }
    }
  }

  static std::optional<std::pair<instruction, unsigned int>>
  disassemble2(const List<unsigned int> &rom0, unsigned int addr);
  static inline const unsigned int test_disassemble_next_address =
      []() -> unsigned int {
    auto _cs = disassemble2(
        List<unsigned int>::cons(
            0u, List<unsigned int>::cons(
                    7u, List<unsigned int>::cons(
                            9u, List<unsigned int>::cons(
                                    11u, List<unsigned int>::nil())))),
        0u);
    if (_cs.has_value()) {
      const std::pair<instruction, unsigned int> &p = *_cs;
      const instruction &_x = p.first;
      const unsigned int &next = p.second;
      return next;
    } else {
      return 0u;
    }
  }();
  static instruction decode3(unsigned int b1, unsigned int b2);
  static std::optional<std::pair<instruction, unsigned int>>
  disassemble3(const List<unsigned int> &rom0, unsigned int addr);

  template <typename T1> static bool is_none(const std::optional<T1> &o) {
    if (o.has_value()) {
      const T1 &_x = *o;
      return false;
    } else {
      return true;
    }
  }

  static inline const bool test_disassemble_short_rom_none =
      is_none<std::pair<instruction, unsigned int>>(disassemble3(
          List<unsigned int>::cons(9u, List<unsigned int>::nil()), 0u));
  static instruction decode4(unsigned int b1, unsigned int b2);
  static std::optional<std::pair<instruction, unsigned int>>
  disassemble4(const List<unsigned int> &rom0, unsigned int addr);

  struct state {
    List<unsigned int> regs;
    List<unsigned int> rom;

    // ACCESSORS
    state clone() const {
      return state{(*this).regs.clone(), (*this).rom.clone()};
    }
  };

  static inline const state init_state =
      state{ListDef::template repeat<unsigned int>(0u, 16u),
            ListDef::template repeat<unsigned int>(0u, 4096u)};
  static inline const unsigned int test_decode_disassemble_1 =
      []() -> unsigned int {
    auto _cs = disassemble4(
        List<unsigned int>::cons(
            0u, List<unsigned int>::cons(
                    7u, List<unsigned int>::cons(
                            9u, List<unsigned int>::cons(
                                    11u, List<unsigned int>::nil())))),
        0u);
    if (_cs.has_value()) {
      const std::pair<instruction, unsigned int> &p = *_cs;
      const instruction &_x = p.first;
      const unsigned int &next = p.second;
      return next;
    } else {
      return 0u;
    }
  }();
  static inline const unsigned int test_decode_disassemble_2 =
      []() -> unsigned int {
    auto _cs = disassemble4(
        List<unsigned int>::cons(
            0u, List<unsigned int>::cons(
                    7u, List<unsigned int>::cons(
                            9u, List<unsigned int>::cons(
                                    11u, List<unsigned int>::nil())))),
        0u);
    if (_cs.has_value()) {
      const std::pair<instruction, unsigned int> &p = *_cs;
      const instruction &_x = p.first;
      const unsigned int &next = p.second;
      return next;
    } else {
      return 0u;
    }
  }();
  static inline const unsigned int test_init_state_regs =
      init_state.regs.length();
  static inline const unsigned int test_init_state_rom =
      init_state.rom.length();
  static inline const std::pair<
      std::pair<
          std::pair<
              std::pair<std::pair<std::pair<unsigned int, unsigned int>, bool>,
                        unsigned int>,
              unsigned int>,
          unsigned int>,
      unsigned int>
      t = std::make_pair(
          std::make_pair(
              std::make_pair(
                  std::make_pair(
                      std::make_pair(
                          std::make_pair(test_disassemble_drop_window,
                                         test_disassemble_next_address),
                          test_disassemble_short_rom_none),
                      test_decode_disassemble_1),
                  test_decode_disassemble_2),
              test_init_state_regs),
          test_init_state_rom);
};

template <typename T1> List<T1> ListDef::repeat(T1 x, unsigned int n) {
  if (n <= 0) {
    return List<T1>::nil();
  } else {
    unsigned int k = n - 1;
    return List<T1>::cons(x, ListDef::template repeat<T1>(x, k));
  }
}

#endif // INCLUDED_DISASSEMBLE_OPS
