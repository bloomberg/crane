#ifndef INCLUDED_RAM_STATE_OPS
#define INCLUDED_RAM_STATE_OPS

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
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
      : v_(crane_convert_spine(
            _other, std::shared_ptr<List<A>>(nullptr),
            [](const List<CraneU> &_cell) -> const List<CraneU> * {
              if (std::holds_alternative<typename List<CraneU>::Cons>(
                      _cell.v())) {
                return std::get<typename List<CraneU>::Cons>(_cell.v()).l.get();
              } else {
                return nullptr;
              }
            },
            [&](const List<CraneU> &_other,
                std::shared_ptr<List<A>> _below) -> variant_t {
              if (std::holds_alternative<typename List<CraneU>::Nil>(
                      _other.v())) {
                return Nil{};
              } else {
                const auto &[a, l] =
                    std::get<typename List<CraneU>::Cons>(_other.v());
                return Cons{
                    [&]() -> A {
                      if constexpr (crane_convertible<A, const CraneU &>) {
                        return crane_convert<A>(a);
                      } else {
                        throw std::logic_error(
                            "unreachable: inactive constructor field at this "
                            "instantiation");
                      }
                    }(),
                    std::move(_below)};
              }
            },
            [](auto &&_alt) {
              return std::make_shared<List<A>>(std::move(_alt));
            })) {}

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
  template <typename T1>
  static T1 nth(uint64_t n, const List<T1> &l, T1 default0);
};

struct RamStateOps {
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
  static inline const state init_state =
      state{ListDef::template repeat<uint64_t>(UINT64_C(0), UINT64_C(16)),
            UINT64_C(0),
            false,
            UINT64_C(0),
            List<uint64_t>::nil(),
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
  static state reset_state(const state &s);
  static uint64_t get_main(const ram_reg &rg, uint64_t i);
  static uint64_t get_stat(const ram_reg &rg, uint64_t i);
  static ram_reg upd_main_in_reg(const ram_reg &rg, uint64_t i, uint64_t v);
  static ram_reg upd_stat_in_reg(const ram_reg &rg, uint64_t i, uint64_t v);
  static ram_reg get_regRAM(const ram_chip &ch, uint64_t r);
  static ram_chip upd_reg_in_chip(const ram_chip &ch, uint64_t r,
                                  const ram_reg &rg);
  static ram_chip upd_port_in_chip(const ram_chip &ch, uint64_t v);
  static ram_chip get_chip(const ram_bank &bk, uint64_t c);
  static ram_bank upd_chip_in_bank(const ram_bank &bk, uint64_t c,
                                   const ram_chip &ch);
  static ram_bank get_bank_from_sys(const List<ram_bank> &sys, uint64_t b);
  static List<ram_bank> upd_bank_in_sys(const state &s, uint64_t b,
                                        const ram_bank &bk);
  static ram_bank current_bank(const state &s);
  static ram_chip current_chip(const state &s);
  static ram_reg current_reg(const state &s);
  static uint64_t ram_read_main(const state &s);
  static List<ram_bank> ram_write_main_sys(const state &s, uint64_t v);
  static List<ram_bank> ram_write_status_sys(const state &s, uint64_t idx,
                                             uint64_t v);
  static std::pair<std::optional<uint64_t>, state> pop_stack(const state &s);
  static inline const state stack_state = state{
      ListDef::template repeat<uint64_t>(UINT64_C(0), UINT64_C(16)),
      UINT64_C(0),
      false,
      UINT64_C(0),
      List<uint64_t>::cons(
          UINT64_C(17),
          List<uint64_t>::cons(
              UINT64_C(255),
              List<uint64_t>::cons(UINT64_C(4095), List<uint64_t>::nil()))),
      empty_ram,
      default_sel,
      ListDef::template repeat<uint64_t>(UINT64_C(0), UINT64_C(8))};
  static inline const state cleared_state =
      state{ListDef::template repeat<uint64_t>(UINT64_C(0), UINT64_C(16)),
            UINT64_C(7),
            true,
            UINT64_C(99),
            List<uint64_t>::cons(UINT64_C(300), List<uint64_t>::nil()),
            empty_ram,
            ram_sel{UINT64_C(3), UINT64_C(2), UINT64_C(1), UINT64_C(7)},
            ListDef::template repeat<uint64_t>(UINT64_C(0), UINT64_C(8))};
  static inline const ram_reg patched_reg =
      upd_main_in_reg(empty_reg, UINT64_C(0), UINT64_C(13));
  static inline const ram_chip patched_chip =
      upd_reg_in_chip(empty_chip, UINT64_C(1), patched_reg);
  static inline const ram_bank patched_bank = upd_chip_in_bank(
      empty_bank, UINT64_C(2), upd_port_in_chip(empty_chip, UINT64_C(9)));
  static inline const List<ram_bank> patched_system =
      upd_bank_in_sys(init_state, UINT64_C(3), patched_bank);
  static constexpr uint64_t t = UINT64_C(0);
};

template <typename T1> List<T1> ListDef::repeat(const T1 &x, uint64_t n) {
  if (n <= 0) {
    return List<T1>::nil();
  } else {
    uint64_t k = n - 1;
    return List<T1>::cons(x, ListDef::template repeat<T1>(x, k));
  }
}

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
      return ListDef::template nth<T1>(m, *a10, std::move(default0));
    }
  }
}

#endif // INCLUDED_RAM_STATE_OPS
