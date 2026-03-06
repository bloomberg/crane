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

struct RamStatusWriteChain {
  struct ram_reg {
    std::shared_ptr<List<unsigned int>> reg_status;
  };

  static std::shared_ptr<List<unsigned int>>
  reg_status(const std::shared_ptr<ram_reg> &r);

  struct ram_chip {
    std::shared_ptr<List<std::shared_ptr<ram_reg>>> chip_regs;
  };

  static std::shared_ptr<List<std::shared_ptr<ram_reg>>>
  chip_regs(const std::shared_ptr<ram_chip> &r);

  struct ram_bank {
    std::shared_ptr<List<std::shared_ptr<ram_chip>>> bank_chips;
  };

  static std::shared_ptr<List<std::shared_ptr<ram_chip>>>
  bank_chips(const std::shared_ptr<ram_bank> &r);

  struct state {
    std::shared_ptr<List<std::shared_ptr<ram_bank>>> ram_sys;
    unsigned int cur_bank;
    unsigned int sel_chip;
    unsigned int sel_reg;
  };

  static std::shared_ptr<List<std::shared_ptr<ram_bank>>>
  ram_sys(const std::shared_ptr<state> &s);

  static unsigned int cur_bank(const std::shared_ptr<state> &s);

  static unsigned int sel_chip(const std::shared_ptr<state> &s);

  static unsigned int sel_reg(const std::shared_ptr<state> &s);

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
                                     std::shared_ptr<List<T1>> xs = _args._a1;
                                     return List<T1>::ctor::cons_(
                                         y,
                                         update_nth<T1>(n_, x, std::move(xs)));
                                   }},
                        l->v());
    }
  }

  static std::shared_ptr<ram_bank> get_bank(const std::shared_ptr<state> &s,
                                            const unsigned int b);

  static std::shared_ptr<ram_chip> get_chip(const std::shared_ptr<ram_bank> &bk,
                                            const unsigned int c);

  static std::shared_ptr<ram_reg> get_reg(const std::shared_ptr<ram_chip> &ch,
                                          const unsigned int r);

  static std::shared_ptr<ram_reg> upd_status_in_reg(std::shared_ptr<ram_reg> rg,
                                                    const unsigned int i,
                                                    const unsigned int v);

  static std::shared_ptr<ram_chip> upd_reg_in_chip(std::shared_ptr<ram_chip> ch,
                                                   const unsigned int r,
                                                   std::shared_ptr<ram_reg> rg);

  static std::shared_ptr<ram_bank>
  upd_chip_in_bank(std::shared_ptr<ram_bank> bk, const unsigned int c,
                   std::shared_ptr<ram_chip> ch);

  static std::shared_ptr<List<std::shared_ptr<ram_bank>>>
  upd_bank_in_sys(const std::shared_ptr<state> &s, const unsigned int b,
                  const std::shared_ptr<ram_bank> &bk);

  static std::shared_ptr<List<std::shared_ptr<ram_bank>>>
  ram_write_status_sys(const std::shared_ptr<state> &s, const unsigned int idx,
                       const unsigned int v);

  static inline const unsigned int t = [](void) {
    std::shared_ptr<ram_reg> rg0 =
        std::make_shared<ram_reg>(ram_reg{List<unsigned int>::ctor::cons_(
            0, List<unsigned int>::ctor::cons_(
                   0, List<unsigned int>::ctor::cons_(
                          0, List<unsigned int>::ctor::cons_(
                                 0, List<unsigned int>::ctor::nil_()))))});
    std::shared_ptr<ram_chip> ch0 = std::make_shared<ram_chip>(
        ram_chip{List<std::shared_ptr<ram_reg>>::ctor::cons_(
            std::move(rg0), List<std::shared_ptr<ram_reg>>::ctor::nil_())});
    std::shared_ptr<ram_bank> bk0 = std::make_shared<ram_bank>(
        ram_bank{List<std::shared_ptr<ram_chip>>::ctor::cons_(
            std::move(ch0), List<std::shared_ptr<ram_chip>>::ctor::nil_())});
    std::unique_ptr<state> s = std::make_unique<state>(state{
        List<std::shared_ptr<ram_bank>>::ctor::cons_(
            std::move(bk0), List<std::shared_ptr<ram_bank>>::ctor::nil_()),
        0, 0, 0});
    std::shared_ptr<List<std::shared_ptr<ram_bank>>> sys_ =
        ram_write_status_sys(
            std::move(s), ((0 + 1) + 1),
            (((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                             1) +
                            1) +
                           1) +
                          1) +
                         1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1) +
                1) +
               1) +
              1) +
             1));
    std::shared_ptr<ram_bank> bk_ = std::move(sys_)->nth(
        0, std::make_shared<ram_bank>(
               ram_bank{List<std::shared_ptr<ram_chip>>::ctor::nil_()}));
    std::shared_ptr<ram_chip> ch_ = std::move(bk_)->bank_chips->nth(
        0, std::make_shared<ram_chip>(
               ram_chip{List<std::shared_ptr<ram_reg>>::ctor::nil_()}));
    std::shared_ptr<ram_reg> rg_ = std::move(ch_)->chip_regs->nth(
        0,
        std::make_shared<ram_reg>(ram_reg{List<unsigned int>::ctor::nil_()}));
    return std::move(rg_)->reg_status->nth(((0 + 1) + 1), 0);
  }();
};
