#ifndef INCLUDED_DISASSEMBLE_OPS
#define INCLUDED_DISASSEMBLE_OPS

#include <any>
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
  template <typename T1> static List<T1> repeat(T1 x, uint64_t n);
};

struct DisassembleOps {
  struct instruction {
    // TYPES
    struct NOP {};

    struct NOP2 {};

    struct LDM {
      uint64_t a0;
    };

    struct LDM2 {
      uint64_t a0;
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

    static instruction nop() { return instruction(NOP{}); }

    static instruction nop2() { return instruction(NOP2{}); }

    static instruction ldm(uint64_t a0) { return instruction(LDM{a0}); }

    static instruction ldm2(uint64_t a0) { return instruction(LDM2{a0}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F2, typename F3>
    requires std::is_invocable_r_v<T1, F2 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F3 &, uint64_t &>
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
    requires std::is_invocable_r_v<T1, F2 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F3 &, uint64_t &>
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

  static instruction decode1(uint64_t b1, uint64_t b2);
  static List<uint64_t> drop_(uint64_t n, List<uint64_t> l);
  static std::optional<std::pair<instruction, uint64_t>>
  disassemble1(const List<uint64_t> &rom0, uint64_t addr);
  static inline const uint64_t test_disassemble_drop_window = []() -> uint64_t {
    auto _cs = disassemble1(
        List<uint64_t>::cons(
            UINT64_C(1),
            List<uint64_t>::cons(
                UINT64_C(2),
                List<uint64_t>::cons(
                    UINT64_C(3),
                    List<uint64_t>::cons(
                        UINT64_C(4),
                        List<uint64_t>::cons(UINT64_C(5),
                                             List<uint64_t>::nil()))))),
        UINT64_C(1));
    if (_cs.has_value()) {
      const std::pair<instruction, uint64_t> &p = *_cs;
      const instruction &_x = p.first;
      const uint64_t &next = p.second;
      return next;
    } else {
      return UINT64_C(0);
    }
  }();
  static instruction decode2(uint64_t b1, uint64_t b2);

  template <typename T1> static List<T1> drop(uint64_t n, List<T1> l) {
    if (n <= 0) {
      return l;
    } else {
      uint64_t n_ = n - 1;
      if (std::holds_alternative<typename List<T1>::Nil>(l.v_mut())) {
        return List<T1>::nil();
      } else {
        auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v_mut());
        return drop<T1>(n_, *a1);
      }
    }
  }

  static std::optional<std::pair<instruction, uint64_t>>
  disassemble2(const List<uint64_t> &rom0, uint64_t addr);
  static inline const uint64_t test_disassemble_next_address =
      []() -> uint64_t {
    auto _cs = disassemble2(
        List<uint64_t>::cons(
            UINT64_C(0),
            List<uint64_t>::cons(
                UINT64_C(7),
                List<uint64_t>::cons(
                    UINT64_C(9), List<uint64_t>::cons(UINT64_C(11),
                                                      List<uint64_t>::nil())))),
        UINT64_C(0));
    if (_cs.has_value()) {
      const std::pair<instruction, uint64_t> &p = *_cs;
      const instruction &_x = p.first;
      const uint64_t &next = p.second;
      return next;
    } else {
      return UINT64_C(0);
    }
  }();
  static instruction decode3(uint64_t b1, uint64_t b2);
  static std::optional<std::pair<instruction, uint64_t>>
  disassemble3(const List<uint64_t> &rom0, uint64_t addr);

  template <typename T1> static bool is_none(const std::optional<T1> &o) {
    if (o.has_value()) {
      const T1 &_x = *o;
      return false;
    } else {
      return true;
    }
  }

  static inline const bool test_disassemble_short_rom_none =
      is_none<std::pair<instruction, uint64_t>>(
          disassemble3(List<uint64_t>::cons(UINT64_C(9), List<uint64_t>::nil()),
                       UINT64_C(0)));
  static instruction decode4(uint64_t b1, uint64_t b2);
  static std::optional<std::pair<instruction, uint64_t>>
  disassemble4(const List<uint64_t> &rom0, uint64_t addr);

  struct state {
    List<uint64_t> regs;
    List<uint64_t> rom;
  };

  static inline const state init_state =
      state{ListDef::template repeat<uint64_t>(UINT64_C(0), UINT64_C(16)),
            ListDef::template repeat<uint64_t>(UINT64_C(0), UINT64_C(4096))};
  static inline const uint64_t test_decode_disassemble_1 = []() -> uint64_t {
    auto _cs = disassemble4(
        List<uint64_t>::cons(
            UINT64_C(0),
            List<uint64_t>::cons(
                UINT64_C(7),
                List<uint64_t>::cons(
                    UINT64_C(9), List<uint64_t>::cons(UINT64_C(11),
                                                      List<uint64_t>::nil())))),
        UINT64_C(0));
    if (_cs.has_value()) {
      const std::pair<instruction, uint64_t> &p = *_cs;
      const instruction &_x = p.first;
      const uint64_t &next = p.second;
      return next;
    } else {
      return UINT64_C(0);
    }
  }();
  static inline const uint64_t test_decode_disassemble_2 = []() -> uint64_t {
    auto _cs = disassemble4(
        List<uint64_t>::cons(
            UINT64_C(0),
            List<uint64_t>::cons(
                UINT64_C(7),
                List<uint64_t>::cons(
                    UINT64_C(9), List<uint64_t>::cons(UINT64_C(11),
                                                      List<uint64_t>::nil())))),
        UINT64_C(0));
    if (_cs.has_value()) {
      const std::pair<instruction, uint64_t> &p = *_cs;
      const instruction &_x = p.first;
      const uint64_t &next = p.second;
      return next;
    } else {
      return UINT64_C(0);
    }
  }();
  static inline const uint64_t test_init_state_regs = init_state.regs.length();
  static inline const uint64_t test_init_state_rom = init_state.rom.length();
  static inline const std::pair<
      std::pair<
          std::pair<std::pair<std::pair<std::pair<uint64_t, uint64_t>, bool>,
                              uint64_t>,
                    uint64_t>,
          uint64_t>,
      uint64_t>
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

template <typename T1> List<T1> ListDef::repeat(T1 x, uint64_t n) {
  if (n <= 0) {
    return List<T1>::nil();
  } else {
    uint64_t k = n - 1;
    return List<T1>::cons(x, ListDef::template repeat<T1>(x, k));
  }
}

#endif // INCLUDED_DISASSEMBLE_OPS
