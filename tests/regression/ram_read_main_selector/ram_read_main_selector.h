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
  A nth(const unsigned int n, const A default0) const {
    if (n <= 0) {
      return std::visit(Overloaded{[&](const typename List<A>::nil _args) -> A {
                                     return default0;
                                   },
                                   [](const typename List<A>::cons _args) -> A {
                                     A x = _args._a0;
                                     return x;
                                   }},
                        this->v());
    } else {
      unsigned int m = n - 1;
      return std::visit(
          Overloaded{
              [&](const typename List<A>::nil _args) -> A { return default0; },
              [&](const typename List<A>::cons _args) -> A {
                std::shared_ptr<List<A>> l_ = _args._a1;
                return std::move(l_)->nth(m, default0);
              }},
          this->v());
    }
  }
};

struct RamReadMainSelector {
  struct ram_reg {
    std::shared_ptr<List<unsigned int>> reg_main;
    std::shared_ptr<List<unsigned int>> reg_status;
  };

  static std::shared_ptr<List<unsigned int>>
  reg_main(const std::shared_ptr<ram_reg> &r);

  static std::shared_ptr<List<unsigned int>>
  reg_status(const std::shared_ptr<ram_reg> &r);

  struct ram_chip {
    std::shared_ptr<List<std::shared_ptr<ram_reg>>> chip_regs;
    unsigned int chip_port;
  };

  static std::shared_ptr<List<std::shared_ptr<ram_reg>>>
  chip_regs(const std::shared_ptr<ram_chip> &r);

  static unsigned int chip_port(const std::shared_ptr<ram_chip> &r);

  struct ram_bank {
    std::shared_ptr<List<std::shared_ptr<ram_chip>>> bank_chips;
  };

  static std::shared_ptr<List<std::shared_ptr<ram_chip>>>
  bank_chips(const std::shared_ptr<ram_bank> &r);

  struct ram_sel {
    unsigned int sel_chip;
    unsigned int sel_reg;
    unsigned int sel_char;
  };

  static unsigned int sel_chip(const std::shared_ptr<ram_sel> &r);

  static unsigned int sel_reg(const std::shared_ptr<ram_sel> &r);

  static unsigned int sel_char(const std::shared_ptr<ram_sel> &r);

  struct state {
    std::shared_ptr<List<std::shared_ptr<ram_bank>>> ram_sys;
    unsigned int cur_bank;
    std::shared_ptr<ram_sel> sel_ram;
  };

  static std::shared_ptr<List<std::shared_ptr<ram_bank>>>
  ram_sys(const std::shared_ptr<state> &s);

  static unsigned int cur_bank(const std::shared_ptr<state> &s);

  static std::shared_ptr<ram_sel> sel_ram(const std::shared_ptr<state> &s);

  static inline const std::shared_ptr<ram_reg> empty_reg =
      std::make_shared<ram_reg>(ram_reg{List<unsigned int>::ctor::nil_(),
                                        List<unsigned int>::ctor::nil_()});

  static inline const std::shared_ptr<ram_chip> empty_chip =
      std::make_shared<ram_chip>(
          ram_chip{List<std::shared_ptr<ram_reg>>::ctor::nil_(), 0});

  static inline const std::shared_ptr<ram_bank> empty_bank =
      std::make_shared<ram_bank>(
          ram_bank{List<std::shared_ptr<ram_chip>>::ctor::nil_()});

  static std::shared_ptr<ram_bank> get_bank(const std::shared_ptr<state> &s,
                                            const unsigned int b);

  static std::shared_ptr<ram_chip> get_chip(const std::shared_ptr<ram_bank> &bk,
                                            const unsigned int c);

  static std::shared_ptr<ram_reg>
  get_regRAM(const std::shared_ptr<ram_chip> &ch, const unsigned int r);

  static unsigned int get_main(const std::shared_ptr<ram_reg> &rg,
                               const unsigned int i);

  static unsigned int ram_read_main(const std::shared_ptr<state> &s);

  static inline const std::shared_ptr<ram_reg> sample_reg =
      std::make_shared<ram_reg>(ram_reg{
          List<unsigned int>::ctor::cons_(
              (((((0 + 1) + 1) + 1) + 1) + 1),
              List<unsigned int>::ctor::cons_(
                  ((((((0 + 1) + 1) + 1) + 1) + 1) + 1),
                  List<unsigned int>::ctor::cons_(
                      (((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1),
                      List<unsigned int>::ctor::cons_(
                          ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
                          List<unsigned int>::ctor::nil_())))),
          List<unsigned int>::ctor::cons_(
              0, List<unsigned int>::ctor::cons_(
                     0, List<unsigned int>::ctor::cons_(
                            0, List<unsigned int>::ctor::cons_(
                                   0, List<unsigned int>::ctor::nil_()))))});

  static inline const std::shared_ptr<ram_chip> sample_chip =
      std::make_shared<ram_chip>(ram_chip{
          List<std::shared_ptr<ram_reg>>::ctor::cons_(
              sample_reg, List<std::shared_ptr<ram_reg>>::ctor::nil_()),
          (((0 + 1) + 1) + 1)});

  static inline const std::shared_ptr<ram_bank> sample_bank =
      std::make_shared<ram_bank>(
          ram_bank{List<std::shared_ptr<ram_chip>>::ctor::cons_(
              sample_chip, List<std::shared_ptr<ram_chip>>::ctor::nil_())});

  static inline const std::shared_ptr<ram_sel> sample_sel =
      std::make_shared<ram_sel>(ram_sel{0, 0, ((0 + 1) + 1)});

  static inline const std::shared_ptr<state> sample_state =
      std::make_shared<state>(
          state{List<std::shared_ptr<ram_bank>>::ctor::cons_(
                    sample_bank, List<std::shared_ptr<ram_bank>>::ctor::nil_()),
                0, sample_sel});

  static inline const unsigned int t = ram_read_main(sample_state);
};
