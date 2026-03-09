#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename A> struct List {
public:
  struct nil {};
  struct cons {
    A _a0;
    std::shared_ptr<List<A>> _a1;
  };
  using variant_t = std::variant<nil, cons>;

private:
  variant_t v_;
  explicit List(nil _v) : v_(std::move(_v)) {}
  explicit List(cons _v) : v_(std::move(_v)) {}

public:
  struct ctor {
    ctor() = delete;
    static std::shared_ptr<List<A>> nil_() {
      return std::shared_ptr<List<A>>(new List<A>(nil{}));
    }
    static std::shared_ptr<List<A>> cons_(A a0,
                                          const std::shared_ptr<List<A>> &a1) {
      return std::shared_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
    static std::unique_ptr<List<A>> nil_uptr() {
      return std::unique_ptr<List<A>>(new List<A>(nil{}));
    }
    static std::unique_ptr<List<A>>
    cons_uptr(A a0, const std::shared_ptr<List<A>> &a1) {
      return std::unique_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
  };
  const variant_t &v() const { return v_; }
  variant_t &v_mut() { return v_; }
};

struct ListDef {
  template <typename T1>
  static std::shared_ptr<List<T1>> repeat(const T1 x, const unsigned int n);
};

struct RamBadState {
  template <typename T1>
  static std::shared_ptr<List<T1>>
  update_nth(const unsigned int n, const T1 x,
             const std::shared_ptr<List<T1>> &l) {
    if (n <= 0) {
      return std::visit(Overloaded{[](const typename List<T1>::nil _args)
                                       -> std::shared_ptr<List<T1>> {
                                     return List<T1>::ctor::nil_();
                                   },
                                   [&](const typename List<T1>::cons _args)
                                       -> std::shared_ptr<List<T1>> {
                                     std::shared_ptr<List<T1>> xs = _args._a1;
                                     return List<T1>::ctor::cons_(
                                         x, std::move(xs));
                                   }},
                        l->v());
    } else {
      unsigned int n_ = n - 1;
      return std::visit(Overloaded{[](const typename List<T1>::nil _args)
                                       -> std::shared_ptr<List<T1>> {
                                     return List<T1>::ctor::nil_();
                                   },
                                   [&](const typename List<T1>::cons _args)
                                       -> std::shared_ptr<List<T1>> {
                                     T1 y = _args._a0;
                                     std::shared_ptr<List<T1>> ys = _args._a1;
                                     return List<T1>::ctor::cons_(
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
      std::make_shared<ram_reg>(ram_reg{ListDef::repeat<unsigned int>(0u, 16u),
                                        ListDef::repeat<unsigned int>(0u, 4u)});

  static inline const std::shared_ptr<ram_chip> empty_chip =
      std::make_shared<ram_chip>(ram_chip{
          ListDef::repeat<std::shared_ptr<ram_reg>>(empty_reg, 4u), 0u});

  static inline const std::shared_ptr<ram_bank> empty_bank =
      std::make_shared<ram_bank>(
          ram_bank{ListDef::repeat<std::shared_ptr<ram_chip>>(empty_chip, 4u)});

  static inline const std::shared_ptr<List<std::shared_ptr<ram_bank>>>
      empty_ram = ListDef::repeat<std::shared_ptr<ram_bank>>(empty_bank, 4u);

  static inline const std::shared_ptr<ram_sel> default_sel =
      std::make_shared<ram_sel>(ram_sel{0u, 0u, 0u, 0u});

  static inline const std::shared_ptr<state> bad_state_acc_overflow =
      std::make_shared<state>(state{ListDef::repeat<unsigned int>(0u, 16u), 16u,
                                    false, 0u, List<unsigned int>::ctor::nil_(),
                                    empty_ram, default_sel,
                                    ListDef::repeat<unsigned int>(0u, 8u)});

  static inline const std::shared_ptr<state> bad_state_pc_overflow =
      std::make_shared<state>(
          state{ListDef::repeat<unsigned int>(0u, 16u), 0u, false, 4096u,
                List<unsigned int>::ctor::nil_(), empty_ram, default_sel,
                ListDef::repeat<unsigned int>(0u, 8u)});

  static inline const std::shared_ptr<state> bad_state_stack_overflow =
      std::make_shared<state>(state{
          ListDef::repeat<unsigned int>(0u, 16u), 0u, false, 0u,
          List<unsigned int>::ctor::cons_(
              0u, List<unsigned int>::ctor::cons_(
                      1u, List<unsigned int>::ctor::cons_(
                              2u, List<unsigned int>::ctor::cons_(
                                      3u, List<unsigned int>::ctor::nil_())))),
          empty_ram, default_sel, ListDef::repeat<unsigned int>(0u, 8u)});

  static inline const std::shared_ptr<state> bad_state_wrong_reg_count =
      std::make_shared<state>(state{ListDef::repeat<unsigned int>(0u, 15u), 0u,
                                    false, 0u, List<unsigned int>::ctor::nil_(),
                                    empty_ram, default_sel,
                                    ListDef::repeat<unsigned int>(0u, 8u)});

  static inline const unsigned int overflow_acc =
      bad_state_acc_overflow->state_acc;
};

template <typename T1>
std::shared_ptr<List<T1>> ListDef::repeat(const T1 x, const unsigned int n) {
  if (n <= 0) {
    return List<T1>::ctor::nil_();
  } else {
    unsigned int k = n - 1;
    return List<T1>::ctor::cons_(x, ListDef::repeat<T1>(x, k));
  }
}
