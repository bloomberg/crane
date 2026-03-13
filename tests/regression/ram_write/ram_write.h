#ifndef INCLUDED_RAM_WRITE
#define INCLUDED_RAM_WRITE

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<t_A>> Nil_() {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::shared_ptr<List<t_A>>
    Cons_(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }

    static std::unique_ptr<List<t_A>> Nil_uptr() {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::unique_ptr<List<t_A>>
    Cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  t_A nth(const unsigned int n, const t_A default0) const {
    if (n <= 0) {
      return std::visit(
          Overloaded{[&](const typename List<t_A>::Nil _args) -> t_A {
                       return default0;
                     },
                     [](const typename List<t_A>::Cons _args) -> t_A {
                       t_A x = _args.d_a0;
                       return x;
                     }},
          this->v());
    } else {
      unsigned int m = n - 1;
      return std::visit(
          Overloaded{[&](const typename List<t_A>::Nil _args) -> t_A {
                       return default0;
                     },
                     [&](const typename List<t_A>::Cons _args) -> t_A {
                       std::shared_ptr<List<t_A>> l_ = _args.d_a1;
                       return std::move(l_)->nth(m, default0);
                     }},
          this->v());
    }
  }

  __attribute__((pure)) unsigned int length() const {
    return std::visit(
        Overloaded{[](const typename List<t_A>::Nil _args) -> unsigned int {
                     return 0u;
                   },
                   [](const typename List<t_A>::Cons _args) -> unsigned int {
                     std::shared_ptr<List<t_A>> l_ = _args.d_a1;
                     return (std::move(l_)->length() + 1);
                   }},
        this->v());
  }
};

struct ListDef {
  template <typename T1>
  static std::shared_ptr<List<T1>> repeat(const T1 x, const unsigned int n);
};

struct RamWrite {
  template <typename T1>
  static std::shared_ptr<List<T1>>
  update_nth(const unsigned int n, const T1 x,
             const std::shared_ptr<List<T1>> &l) {
    if (n <= 0) {
      return std::visit(Overloaded{[](const typename List<T1>::Nil _args)
                                       -> std::shared_ptr<List<T1>> {
                                     return List<T1>::ctor::Nil_();
                                   },
                                   [&](const typename List<T1>::Cons _args)
                                       -> std::shared_ptr<List<T1>> {
                                     std::shared_ptr<List<T1>> xs = _args.d_a1;
                                     return List<T1>::ctor::Cons_(
                                         x, std::move(xs));
                                   }},
                        l->v());
    } else {
      unsigned int n_ = n - 1;
      return std::visit(Overloaded{[](const typename List<T1>::Nil _args)
                                       -> std::shared_ptr<List<T1>> {
                                     return List<T1>::ctor::Nil_();
                                   },
                                   [&](const typename List<T1>::Cons _args)
                                       -> std::shared_ptr<List<T1>> {
                                     T1 y = _args.d_a0;
                                     std::shared_ptr<List<T1>> ys = _args.d_a1;
                                     return List<T1>::ctor::Cons_(
                                         y,
                                         update_nth<T1>(n_, x, std::move(ys)));
                                   }},
                        l->v());
    }
  }

  struct ram_reg {
    std::shared_ptr<List<unsigned int>> reg_main;
    std::shared_ptr<List<unsigned int>> reg_status;
  };

  struct ram_chip {
    std::shared_ptr<List<std::shared_ptr<ram_reg>>> chip_regs;
    unsigned int chip_port;
  };

  struct ram_bank {
    std::shared_ptr<List<std::shared_ptr<ram_chip>>> bank_chips;
  };

  struct ram_sel {
    unsigned int sel_bank;
    unsigned int sel_chip;
    unsigned int sel_reg;
    unsigned int sel_char;
  };

  struct state {
    std::shared_ptr<List<unsigned int>> state_regs;
    unsigned int state_acc;
    bool state_carry;
    unsigned int state_pc;
    std::shared_ptr<List<unsigned int>> state_stack;
    std::shared_ptr<List<std::shared_ptr<ram_bank>>> state_ram;
    std::shared_ptr<ram_sel> state_sel;
    std::shared_ptr<List<unsigned int>> state_rom;
  };

  static inline const std::shared_ptr<ram_reg> empty_reg =
      std::make_shared<ram_reg>(
          ram_reg{ListDef::template repeat<unsigned int>(0u, 16u),
                  ListDef::template repeat<unsigned int>(0u, 4u)});
  static inline const std::shared_ptr<ram_chip> empty_chip =
      std::make_shared<ram_chip>(ram_chip{
          ListDef::template repeat<std::shared_ptr<ram_reg>>(empty_reg, 4u),
          0u});
  static inline const std::shared_ptr<ram_bank> empty_bank =
      std::make_shared<ram_bank>(ram_bank{
          ListDef::template repeat<std::shared_ptr<ram_chip>>(empty_chip, 4u)});
  static inline const std::shared_ptr<List<std::shared_ptr<ram_bank>>>
      empty_ram =
          ListDef::template repeat<std::shared_ptr<ram_bank>>(empty_bank, 4u);
  static inline const std::shared_ptr<ram_sel> default_sel =
      std::make_shared<ram_sel>(ram_sel{0u, 0u, 0u, 0u});
  static inline const std::shared_ptr<state> init_state =
      std::make_shared<state>(
          state{ListDef::template repeat<unsigned int>(0u, 16u), 0u, false, 0u,
                List<unsigned int>::ctor::Nil_(), empty_ram, default_sel,
                ListDef::template repeat<unsigned int>(0u, 8u)});
  __attribute__((pure)) static unsigned int
  get_main(const std::shared_ptr<ram_reg> &rg, const unsigned int i);
  static std::shared_ptr<ram_reg> upd_main_in_reg(std::shared_ptr<ram_reg> rg,
                                                  const unsigned int i,
                                                  const unsigned int v);
  static std::shared_ptr<ram_reg> upd_stat_in_reg(std::shared_ptr<ram_reg> rg,
                                                  const unsigned int i,
                                                  const unsigned int v);
  static std::shared_ptr<ram_reg>
  get_regRAM(const std::shared_ptr<ram_chip> &ch, const unsigned int r);
  static std::shared_ptr<ram_chip> upd_reg_in_chip(std::shared_ptr<ram_chip> ch,
                                                   const unsigned int r,
                                                   std::shared_ptr<ram_reg> rg);
  static std::shared_ptr<ram_chip> get_chip(const std::shared_ptr<ram_bank> &bk,
                                            const unsigned int c);
  static std::shared_ptr<ram_bank>
  upd_chip_in_bank(std::shared_ptr<ram_bank> bk, const unsigned int c,
                   std::shared_ptr<ram_chip> ch);
  static std::shared_ptr<ram_bank>
  get_bank_from_sys(const std::shared_ptr<List<std::shared_ptr<ram_bank>>> &sys,
                    const unsigned int b);
  static std::shared_ptr<List<std::shared_ptr<ram_bank>>>
  upd_bank_in_sys(const std::shared_ptr<state> &s, const unsigned int b,
                  const std::shared_ptr<ram_bank> &bk);
  static std::shared_ptr<ram_bank>
  current_bank(const std::shared_ptr<state> &s);
  static std::shared_ptr<ram_chip>
  current_chip(const std::shared_ptr<state> &s);
  static std::shared_ptr<ram_reg> current_reg(const std::shared_ptr<state> &s);
  __attribute__((pure)) static unsigned int
  ram_read_main(const std::shared_ptr<state> &s);
  static std::shared_ptr<List<std::shared_ptr<ram_bank>>>
  ram_write_main_sys(const std::shared_ptr<state> &s, const unsigned int v);
  static std::shared_ptr<List<std::shared_ptr<ram_bank>>>
  ram_write_status_sys(const std::shared_ptr<state> &s, const unsigned int idx,
                       const unsigned int v);
  static inline const unsigned int write_bank_count =
      ram_write_main_sys(init_state, 12u)->length();
};

template <typename T1>
std::shared_ptr<List<T1>> ListDef::repeat(const T1 x, const unsigned int n) {
  if (n <= 0) {
    return List<T1>::ctor::Nil_();
  } else {
    unsigned int k = n - 1;
    return List<T1>::ctor::Cons_(x, ListDef::template repeat<T1>(x, k));
  }
}

#endif // INCLUDED_RAM_WRITE
