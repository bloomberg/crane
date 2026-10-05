#ifndef INCLUDED_RAM_BAD_STATE
#define INCLUDED_RAM_BAD_STATE

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
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
};

struct ListDef {
  template <typename T1> static List<T1> repeat(const T1 &x, uint64_t n);
};

struct RamBadState {
  template <typename T1>
  static List<T1> update_nth(uint64_t n, const T1 &x, const List<T1> &l) {
    if (n <= 0) {
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(x, *a1);
      }
    } else {
      uint64_t n_ = n - 1;
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[a00, a10] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(a00, update_nth<T1>(n_, x, *a10));
      }
    }
  }

  struct ram_reg {
    List<uint64_t> reg_main;
    List<uint64_t> reg_status;
  };

  struct ram_chip {
    List<ram_reg> chip_regs;
    uint64_t chip_port;
  };

  struct ram_bank {
    List<ram_chip> bank_chips;
  };

  struct ram_sel {
    uint64_t sel_bank;
    uint64_t sel_chip;
    uint64_t sel_reg;
    uint64_t sel_char;
  };

  struct state {
    List<uint64_t> state_regs;
    uint64_t state_acc;
    bool state_carry;
    uint64_t state_pc;
    List<uint64_t> state_stack;
    List<ram_bank> state_ram;
    ram_sel state_sel;
    List<uint64_t> state_rom;
  };

  static inline const ram_reg empty_reg =
      ram_reg{ListDef::template repeat<uint64_t>(UINT64_C(0), UINT64_C(16)),
              ListDef::template repeat<uint64_t>(UINT64_C(0), UINT64_C(4))};
  static inline const ram_chip empty_chip = ram_chip{
      ListDef::template repeat<ram_reg>(empty_reg, UINT64_C(4)), UINT64_C(0)};
  static inline const ram_bank empty_bank =
      ram_bank{ListDef::template repeat<ram_chip>(empty_chip, UINT64_C(4))};
  static inline const List<ram_bank> empty_ram =
      ListDef::template repeat<ram_bank>(empty_bank, UINT64_C(4));
  static inline const ram_sel default_sel =
      ram_sel{UINT64_C(0), UINT64_C(0), UINT64_C(0), UINT64_C(0)};
  static inline const state bad_state_acc_overflow =
      state{ListDef::template repeat<uint64_t>(UINT64_C(0), UINT64_C(16)),
            UINT64_C(16),
            false,
            UINT64_C(0),
            List<uint64_t>::nil(),
            empty_ram,
            default_sel,
            ListDef::template repeat<uint64_t>(UINT64_C(0), UINT64_C(8))};
  static inline const state bad_state_pc_overflow =
      state{ListDef::template repeat<uint64_t>(UINT64_C(0), UINT64_C(16)),
            UINT64_C(0),
            false,
            UINT64_C(4096),
            List<uint64_t>::nil(),
            empty_ram,
            default_sel,
            ListDef::template repeat<uint64_t>(UINT64_C(0), UINT64_C(8))};
  static inline const state bad_state_stack_overflow = state{
      ListDef::template repeat<uint64_t>(UINT64_C(0), UINT64_C(16)),
      UINT64_C(0),
      false,
      UINT64_C(0),
      List<uint64_t>::cons(
          UINT64_C(0),
          List<uint64_t>::cons(
              UINT64_C(1),
              List<uint64_t>::cons(
                  UINT64_C(2),
                  List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil())))),
      empty_ram,
      default_sel,
      ListDef::template repeat<uint64_t>(UINT64_C(0), UINT64_C(8))};
  static inline const state bad_state_wrong_reg_count =
      state{ListDef::template repeat<uint64_t>(UINT64_C(0), UINT64_C(15)),
            UINT64_C(0),
            false,
            UINT64_C(0),
            List<uint64_t>::nil(),
            empty_ram,
            default_sel,
            ListDef::template repeat<uint64_t>(UINT64_C(0), UINT64_C(8))};
  static inline const uint64_t overflow_acc = bad_state_acc_overflow.state_acc;
};

template <typename T1> List<T1> ListDef::repeat(const T1 &x, uint64_t n) {
  if (n <= 0) {
    return List<T1>::nil();
  } else {
    uint64_t k = n - 1;
    return List<T1>::cons(x, ListDef::template repeat<T1>(x, k));
  }
}

#endif // INCLUDED_RAM_BAD_STATE
