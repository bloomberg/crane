#ifndef INCLUDED_DISASSEMBLE_OPS
#define INCLUDED_DISASSEMBLE_OPS

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
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

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) = default;
  List &operator=(List &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  uint64_t length() const {
    const List<A> *_self = this;

    /// CraneEnter: captures varying parameters for each recursive call.
    struct CraneEnter {
      const List<A> *_self;
    };

    /// CraneCont_Cons: resumes after recursive call, then processes rest.
    struct CraneCont_Cons {};

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    uint64_t _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{_self});
    /// Loopified length: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(CraneCont_Cons{});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }
};

struct ListDef {
  template <typename T1> static List<T1> repeat(const T1 &x, uint64_t n);
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
      const auto &[_x, next] = p;
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
      const auto &[_x, next] = p;
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
      const auto &[_x, next] = p;
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
      const auto &[_x, next] = p;
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

template <typename T1> List<T1> ListDef::repeat(const T1 &x, uint64_t n) {
  if (n <= 0) {
    return List<T1>::nil();
  } else {
    uint64_t k = n - 1;
    return List<T1>::cons(x, ListDef::template repeat<T1>(x, k));
  }
}

#endif // INCLUDED_DISASSEMBLE_OPS
