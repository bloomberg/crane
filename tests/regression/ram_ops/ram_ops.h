#ifndef INCLUDED_RAM_OPS
#define INCLUDED_RAM_OPS

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
};

struct RamOps {
  struct ram_reg_main {
    std::shared_ptr<List<unsigned int>> reg_main;
  };

  struct ram_chip_main {
    std::shared_ptr<List<std::shared_ptr<ram_reg_main>>> chip_regs_main;
  };

  struct ram_bank_main {
    std::shared_ptr<List<std::shared_ptr<ram_chip_main>>> bank_chips_main;
  };

  struct state_main {
    std::shared_ptr<List<std::shared_ptr<ram_bank_main>>> ram_sys_main;
    unsigned int cur_bank_main;
    unsigned int sel_chip_main;
    unsigned int sel_reg_main;
    unsigned int sel_char_main;
  };

  template <typename T1>
  static std::shared_ptr<List<T1>>
  update_nth_main(const unsigned int n, const T1 x,
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
      return std::visit(
          Overloaded{[](const typename List<T1>::Nil _args)
                         -> std::shared_ptr<List<T1>> {
                       return List<T1>::ctor::Nil_();
                     },
                     [&](const typename List<T1>::Cons _args)
                         -> std::shared_ptr<List<T1>> {
                       T1 y = _args.d_a0;
                       std::shared_ptr<List<T1>> xs = _args.d_a1;
                       return List<T1>::ctor::Cons_(
                           y, update_nth_main<T1>(n_, x, std::move(xs)));
                     }},
          l->v());
    }
  }

  static std::shared_ptr<ram_bank_main>
  get_bank_main(const std::shared_ptr<state_main> &s, const unsigned int b);
  static std::shared_ptr<ram_chip_main>
  get_chip_main(const std::shared_ptr<ram_bank_main> &bk, const unsigned int c);
  static std::shared_ptr<ram_reg_main>
  get_reg_main(const std::shared_ptr<ram_chip_main> &ch, const unsigned int r);
  static std::shared_ptr<ram_reg_main>
  upd_main_in_reg(std::shared_ptr<ram_reg_main> rg, const unsigned int i,
                  const unsigned int v);
  static std::shared_ptr<ram_chip_main>
  upd_reg_in_chip_main(std::shared_ptr<ram_chip_main> ch, const unsigned int r,
                       std::shared_ptr<ram_reg_main> rg);
  static std::shared_ptr<ram_bank_main>
  upd_chip_in_bank_main(std::shared_ptr<ram_bank_main> bk, const unsigned int c,
                        std::shared_ptr<ram_chip_main> ch);
  static std::shared_ptr<List<std::shared_ptr<ram_bank_main>>>
  upd_bank_in_sys_main(const std::shared_ptr<state_main> &s,
                       const unsigned int b,
                       const std::shared_ptr<ram_bank_main> &bk);
  static std::shared_ptr<List<std::shared_ptr<ram_bank_main>>>
  ram_write_main_sys(const std::shared_ptr<state_main> &s,
                     const unsigned int v);
  static inline const unsigned int test_main_write_chain = [](void) {
    std::shared_ptr<ram_reg_main> rg0 = std::make_shared<ram_reg_main>(
        ram_reg_main{List<unsigned int>::ctor::Cons_(
            0u, List<unsigned int>::ctor::Cons_(
                    0u, List<unsigned int>::ctor::Cons_(
                            0u, List<unsigned int>::ctor::Nil_())))});
    std::shared_ptr<ram_chip_main> ch0 = std::make_shared<ram_chip_main>(
        ram_chip_main{List<std::shared_ptr<ram_reg_main>>::ctor::Cons_(
            std::move(rg0),
            List<std::shared_ptr<ram_reg_main>>::ctor::Nil_())});
    std::shared_ptr<ram_bank_main> bk0 = std::make_shared<ram_bank_main>(
        ram_bank_main{List<std::shared_ptr<ram_chip_main>>::ctor::Cons_(
            std::move(ch0),
            List<std::shared_ptr<ram_chip_main>>::ctor::Nil_())});
    std::unique_ptr<state_main> s = std::make_unique<state_main>(state_main{
        List<std::shared_ptr<ram_bank_main>>::ctor::Cons_(
            std::move(bk0), List<std::shared_ptr<ram_bank_main>>::ctor::Nil_()),
        0u, 0u, 0u, 1u});
    std::shared_ptr<List<std::shared_ptr<ram_bank_main>>> sys_ =
        ram_write_main_sys(std::move(s), 19u);
    std::shared_ptr<ram_bank_main> bk_ = std::move(sys_)->nth(
        0u, std::make_shared<ram_bank_main>(ram_bank_main{
                List<std::shared_ptr<ram_chip_main>>::ctor::Nil_()}));
    std::shared_ptr<ram_chip_main> ch_ = std::move(bk_)->bank_chips_main->nth(
        0u, std::make_shared<ram_chip_main>(ram_chip_main{
                List<std::shared_ptr<ram_reg_main>>::ctor::Nil_()}));
    std::shared_ptr<ram_reg_main> rg_ = std::move(ch_)->chip_regs_main->nth(
        0u, std::make_shared<ram_reg_main>(
                ram_reg_main{List<unsigned int>::ctor::Nil_()}));
    return std::move(rg_)->reg_main->nth(1u, 0u);
  }();

  struct chip_port {
    unsigned int chip_port_val;
  };

  struct bank_port {
    std::shared_ptr<List<std::shared_ptr<chip_port>>> bank_chips_port;
  };

  struct state_port {
    std::shared_ptr<List<std::shared_ptr<bank_port>>> ram_sys_port;
    unsigned int cur_bank_port;
    unsigned int sel_chip_port;
  };

  template <typename T1>
  static std::shared_ptr<List<T1>>
  update_nth_port(const unsigned int n, const T1 x,
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
      return std::visit(
          Overloaded{[](const typename List<T1>::Nil _args)
                         -> std::shared_ptr<List<T1>> {
                       return List<T1>::ctor::Nil_();
                     },
                     [&](const typename List<T1>::Cons _args)
                         -> std::shared_ptr<List<T1>> {
                       T1 y = _args.d_a0;
                       std::shared_ptr<List<T1>> xs = _args.d_a1;
                       return List<T1>::ctor::Cons_(
                           y, update_nth_port<T1>(n_, x, std::move(xs)));
                     }},
          l->v());
    }
  }

  static std::shared_ptr<bank_port>
  get_bank_port(const std::shared_ptr<state_port> &s, const unsigned int b);
  static std::shared_ptr<chip_port>
  get_chip_port(const std::shared_ptr<bank_port> &bk, const unsigned int c);
  static std::shared_ptr<chip_port>
  upd_port_in_chip(const std::shared_ptr<chip_port> &_x, const unsigned int v);
  static std::shared_ptr<bank_port>
  upd_chip_in_bank_port(std::shared_ptr<bank_port> bk, const unsigned int c,
                        std::shared_ptr<chip_port> ch);
  static std::shared_ptr<List<std::shared_ptr<bank_port>>>
  upd_bank_in_sys_port(const std::shared_ptr<state_port> &s,
                       const unsigned int b,
                       const std::shared_ptr<bank_port> &bk);
  static std::shared_ptr<List<std::shared_ptr<bank_port>>>
  ram_write_port_sys(const std::shared_ptr<state_port> &s,
                     const unsigned int v);
  static inline const unsigned int test_port_write_chain = [](void) {
    std::shared_ptr<chip_port> ch0 = std::make_shared<chip_port>(chip_port{0u});
    std::shared_ptr<bank_port> bk0 = std::make_shared<bank_port>(
        bank_port{List<std::shared_ptr<chip_port>>::ctor::Cons_(
            std::move(ch0), List<std::shared_ptr<chip_port>>::ctor::Nil_())});
    std::unique_ptr<state_port> s = std::make_unique<state_port>(state_port{
        List<std::shared_ptr<bank_port>>::ctor::Cons_(
            std::move(bk0), List<std::shared_ptr<bank_port>>::ctor::Nil_()),
        0u, 0u});
    std::shared_ptr<List<std::shared_ptr<bank_port>>> sys_ =
        ram_write_port_sys(std::move(s), 17u);
    std::shared_ptr<bank_port> bk_ = std::move(sys_)->nth(
        0u, std::make_shared<bank_port>(
                bank_port{List<std::shared_ptr<chip_port>>::ctor::Nil_()}));
    std::shared_ptr<chip_port> ch_ = std::move(bk_)->bank_chips_port->nth(
        0u, std::make_shared<chip_port>(chip_port{0u}));
    return std::move(ch_)->chip_port_val;
  }();

  struct ram_reg_status {
    std::shared_ptr<List<unsigned int>> reg_status;
  };

  struct ram_chip_status {
    std::shared_ptr<List<std::shared_ptr<ram_reg_status>>> chip_regs_status;
  };

  struct ram_bank_status {
    std::shared_ptr<List<std::shared_ptr<ram_chip_status>>> bank_chips_status;
  };

  struct state_status {
    std::shared_ptr<List<std::shared_ptr<ram_bank_status>>> ram_sys_status;
    unsigned int cur_bank_status;
    unsigned int sel_chip_status;
    unsigned int sel_reg_status;
  };

  template <typename T1>
  static std::shared_ptr<List<T1>>
  update_nth_status(const unsigned int n, const T1 x,
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
      return std::visit(
          Overloaded{[](const typename List<T1>::Nil _args)
                         -> std::shared_ptr<List<T1>> {
                       return List<T1>::ctor::Nil_();
                     },
                     [&](const typename List<T1>::Cons _args)
                         -> std::shared_ptr<List<T1>> {
                       T1 y = _args.d_a0;
                       std::shared_ptr<List<T1>> xs = _args.d_a1;
                       return List<T1>::ctor::Cons_(
                           y, update_nth_status<T1>(n_, x, std::move(xs)));
                     }},
          l->v());
    }
  }

  static std::shared_ptr<ram_bank_status>
  get_bank_status(const std::shared_ptr<state_status> &s, const unsigned int b);
  static std::shared_ptr<ram_chip_status>
  get_chip_status(const std::shared_ptr<ram_bank_status> &bk,
                  const unsigned int c);
  static std::shared_ptr<ram_reg_status>
  get_reg_status(const std::shared_ptr<ram_chip_status> &ch,
                 const unsigned int r);
  static std::shared_ptr<ram_reg_status>
  upd_status_in_reg(std::shared_ptr<ram_reg_status> rg, const unsigned int i,
                    const unsigned int v);
  static std::shared_ptr<ram_chip_status>
  upd_reg_in_chip_status(std::shared_ptr<ram_chip_status> ch,
                         const unsigned int r,
                         std::shared_ptr<ram_reg_status> rg);
  static std::shared_ptr<ram_bank_status>
  upd_chip_in_bank_status(std::shared_ptr<ram_bank_status> bk,
                          const unsigned int c,
                          std::shared_ptr<ram_chip_status> ch);
  static std::shared_ptr<List<std::shared_ptr<ram_bank_status>>>
  upd_bank_in_sys_status(const std::shared_ptr<state_status> &s,
                         const unsigned int b,
                         const std::shared_ptr<ram_bank_status> &bk);
  static std::shared_ptr<List<std::shared_ptr<ram_bank_status>>>
  ram_write_status_sys(const std::shared_ptr<state_status> &s,
                       const unsigned int idx, const unsigned int v);
  static inline const unsigned int test_status_write_chain = [](void) {
    std::shared_ptr<ram_reg_status> rg0 = std::make_shared<ram_reg_status>(
        ram_reg_status{List<unsigned int>::ctor::Cons_(
            0u, List<unsigned int>::ctor::Cons_(
                    0u, List<unsigned int>::ctor::Cons_(
                            0u, List<unsigned int>::ctor::Cons_(
                                    0u, List<unsigned int>::ctor::Nil_()))))});
    std::shared_ptr<ram_chip_status> ch0 = std::make_shared<ram_chip_status>(
        ram_chip_status{List<std::shared_ptr<ram_reg_status>>::ctor::Cons_(
            std::move(rg0),
            List<std::shared_ptr<ram_reg_status>>::ctor::Nil_())});
    std::shared_ptr<ram_bank_status> bk0 = std::make_shared<ram_bank_status>(
        ram_bank_status{List<std::shared_ptr<ram_chip_status>>::ctor::Cons_(
            std::move(ch0),
            List<std::shared_ptr<ram_chip_status>>::ctor::Nil_())});
    std::unique_ptr<state_status> s = std::make_unique<state_status>(
        state_status{List<std::shared_ptr<ram_bank_status>>::ctor::Cons_(
                         std::move(bk0),
                         List<std::shared_ptr<ram_bank_status>>::ctor::Nil_()),
                     0u, 0u, 0u});
    std::shared_ptr<List<std::shared_ptr<ram_bank_status>>> sys_ =
        ram_write_status_sys(std::move(s), 2u, 25u);
    std::shared_ptr<ram_bank_status> bk_ = std::move(sys_)->nth(
        0u, std::make_shared<ram_bank_status>(ram_bank_status{
                List<std::shared_ptr<ram_chip_status>>::ctor::Nil_()}));
    std::shared_ptr<ram_chip_status> ch_ =
        std::move(bk_)->bank_chips_status->nth(
            0u, std::make_shared<ram_chip_status>(ram_chip_status{
                    List<std::shared_ptr<ram_reg_status>>::ctor::Nil_()}));
    std::shared_ptr<ram_reg_status> rg_ = std::move(ch_)->chip_regs_status->nth(
        0u, std::make_shared<ram_reg_status>(
                ram_reg_status{List<unsigned int>::ctor::Nil_()}));
    return std::move(rg_)->reg_status->nth(2u, 0u);
  }();

  struct ram_reg_sel {
    std::shared_ptr<List<unsigned int>> reg_main_sel;
    std::shared_ptr<List<unsigned int>> reg_status_sel;
  };

  struct ram_chip_sel {
    std::shared_ptr<List<std::shared_ptr<ram_reg_sel>>> chip_regs_sel;
    unsigned int chip_port_sel;
  };

  struct ram_bank_sel {
    std::shared_ptr<List<std::shared_ptr<ram_chip_sel>>> bank_chips_sel;
  };

  struct ram_sel {
    unsigned int sel_chip;
    unsigned int sel_reg;
    unsigned int sel_char;
  };

  struct state_sel {
    std::shared_ptr<List<std::shared_ptr<ram_bank_sel>>> ram_sys_sel;
    unsigned int cur_bank_sel;
    std::shared_ptr<ram_sel> sel_ram;
  };

  static inline const std::shared_ptr<ram_reg_sel> empty_reg_sel =
      std::make_shared<ram_reg_sel>(ram_reg_sel{
          List<unsigned int>::ctor::Nil_(), List<unsigned int>::ctor::Nil_()});
  static inline const std::shared_ptr<ram_chip_sel> empty_chip_sel =
      std::make_shared<ram_chip_sel>(
          ram_chip_sel{List<std::shared_ptr<ram_reg_sel>>::ctor::Nil_(), 0u});
  static inline const std::shared_ptr<ram_bank_sel> empty_bank_sel =
      std::make_shared<ram_bank_sel>(
          ram_bank_sel{List<std::shared_ptr<ram_chip_sel>>::ctor::Nil_()});
  static std::shared_ptr<ram_bank_sel>
  get_bank_sel(const std::shared_ptr<state_sel> &s, const unsigned int b);
  static std::shared_ptr<ram_chip_sel>
  get_chip_sel(const std::shared_ptr<ram_bank_sel> &bk, const unsigned int c);
  static std::shared_ptr<ram_reg_sel>
  get_regRAM(const std::shared_ptr<ram_chip_sel> &ch, const unsigned int r);
  __attribute__((pure)) static unsigned int
  get_main_sel(const std::shared_ptr<ram_reg_sel> &rg, const unsigned int i);
  __attribute__((pure)) static unsigned int
  ram_read_main(const std::shared_ptr<state_sel> &s);
  static inline const std::shared_ptr<ram_reg_sel> sample_reg_sel =
      std::make_shared<ram_reg_sel>(ram_reg_sel{
          List<unsigned int>::ctor::Cons_(
              5u, List<unsigned int>::ctor::Cons_(
                      6u, List<unsigned int>::ctor::Cons_(
                              7u, List<unsigned int>::ctor::Cons_(
                                      8u, List<unsigned int>::ctor::Nil_())))),
          List<unsigned int>::ctor::Cons_(
              0u,
              List<unsigned int>::ctor::Cons_(
                  0u, List<unsigned int>::ctor::Cons_(
                          0u, List<unsigned int>::ctor::Cons_(
                                  0u, List<unsigned int>::ctor::Nil_()))))});
  static inline const std::shared_ptr<ram_chip_sel> sample_chip_sel =
      std::make_shared<ram_chip_sel>(ram_chip_sel{
          List<std::shared_ptr<ram_reg_sel>>::ctor::Cons_(
              sample_reg_sel, List<std::shared_ptr<ram_reg_sel>>::ctor::Nil_()),
          3u});
  static inline const std::shared_ptr<ram_bank_sel> sample_bank_sel =
      std::make_shared<ram_bank_sel>(
          ram_bank_sel{List<std::shared_ptr<ram_chip_sel>>::ctor::Cons_(
              sample_chip_sel,
              List<std::shared_ptr<ram_chip_sel>>::ctor::Nil_())});
  static inline const std::shared_ptr<ram_sel> sample_sel =
      std::make_shared<ram_sel>(ram_sel{0u, 0u, 2u});
  static inline const std::shared_ptr<state_sel> sample_state_sel =
      std::make_shared<state_sel>(
          state_sel{List<std::shared_ptr<ram_bank_sel>>::ctor::Cons_(
                        sample_bank_sel,
                        List<std::shared_ptr<ram_bank_sel>>::ctor::Nil_()),
                    0u, sample_sel});
  static inline const unsigned int test_read_main_selector =
      ram_read_main(sample_state_sel);

  struct ram_reg_nested {
    std::shared_ptr<List<unsigned int>> reg_main_nested;
    std::shared_ptr<List<unsigned int>> reg_status_nested;
  };

  struct ram_chip_nested {
    std::shared_ptr<List<std::shared_ptr<ram_reg_nested>>> chip_regs_nested;
    unsigned int chip_port_nested;
  };

  struct ram_bank_nested {
    std::shared_ptr<List<std::shared_ptr<ram_chip_nested>>> bank_chips_nested;
  };

  struct ram_sel_nested {
    unsigned int sel_chip_nested;
    unsigned int sel_reg_nested;
    unsigned int sel_char_nested;
  };

  struct state_nested {
    std::shared_ptr<List<std::shared_ptr<ram_bank_nested>>> ram_sys_nested;
    unsigned int cur_bank_nested;
    std::shared_ptr<ram_sel_nested> sel_ram_nested;
  };

  static inline const std::shared_ptr<ram_reg_nested> empty_reg_nested =
      std::make_shared<ram_reg_nested>(ram_reg_nested{
          List<unsigned int>::ctor::Nil_(), List<unsigned int>::ctor::Nil_()});
  static inline const std::shared_ptr<ram_chip_nested> empty_chip_nested =
      std::make_shared<ram_chip_nested>(ram_chip_nested{
          List<std::shared_ptr<ram_reg_nested>>::ctor::Nil_(), 0u});
  static inline const std::shared_ptr<ram_bank_nested> empty_bank_nested =
      std::make_shared<ram_bank_nested>(ram_bank_nested{
          List<std::shared_ptr<ram_chip_nested>>::ctor::Nil_()});
  static std::shared_ptr<ram_bank_nested>
  get_bank_nested(const std::shared_ptr<state_nested> &s, const unsigned int b);
  static std::shared_ptr<ram_chip_nested>
  get_chip_nested(const std::shared_ptr<ram_bank_nested> &bk,
                  const unsigned int c);
  static std::shared_ptr<ram_reg_nested>
  get_regRAM_nested(const std::shared_ptr<ram_chip_nested> &ch,
                    const unsigned int r);
  __attribute__((pure)) static unsigned int
  get_main_nested(const std::shared_ptr<ram_reg_nested> &rg,
                  const unsigned int i);
  __attribute__((pure)) static unsigned int
  ram_read_main_nested(const std::shared_ptr<state_nested> &s);
  static inline const std::shared_ptr<ram_reg_nested> sample_reg_nested =
      std::make_shared<ram_reg_nested>(ram_reg_nested{
          List<unsigned int>::ctor::Cons_(
              5u, List<unsigned int>::ctor::Cons_(
                      6u, List<unsigned int>::ctor::Cons_(
                              7u, List<unsigned int>::ctor::Cons_(
                                      8u, List<unsigned int>::ctor::Nil_())))),
          List<unsigned int>::ctor::Cons_(
              0u,
              List<unsigned int>::ctor::Cons_(
                  0u, List<unsigned int>::ctor::Cons_(
                          0u, List<unsigned int>::ctor::Cons_(
                                  0u, List<unsigned int>::ctor::Nil_()))))});
  static inline const std::shared_ptr<ram_chip_nested> sample_chip_nested =
      std::make_shared<ram_chip_nested>(ram_chip_nested{
          List<std::shared_ptr<ram_reg_nested>>::ctor::Cons_(
              sample_reg_nested,
              List<std::shared_ptr<ram_reg_nested>>::ctor::Nil_()),
          3u});
  static inline const std::shared_ptr<ram_bank_nested> sample_bank_nested =
      std::make_shared<ram_bank_nested>(
          ram_bank_nested{List<std::shared_ptr<ram_chip_nested>>::ctor::Cons_(
              sample_chip_nested,
              List<std::shared_ptr<ram_chip_nested>>::ctor::Nil_())});
  static inline const std::shared_ptr<ram_sel_nested> sample_sel_nested =
      std::make_shared<ram_sel_nested>(ram_sel_nested{0u, 0u, 2u});
  static inline const std::shared_ptr<state_nested> sample_state_nested =
      std::make_shared<state_nested>(state_nested{
          List<std::shared_ptr<ram_bank_nested>>::ctor::Cons_(
              sample_bank_nested,
              List<std::shared_ptr<ram_bank_nested>>::ctor::Nil_()),
          0u, sample_sel_nested});
  static inline const unsigned int test_read_nested =
      ram_read_main_nested(sample_state_nested);

  template <typename T1>
  static std::shared_ptr<List<T1>>
  update_nth_frame(const unsigned int n, const T1 x,
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
      return std::visit(
          Overloaded{[](const typename List<T1>::Nil _args)
                         -> std::shared_ptr<List<T1>> {
                       return List<T1>::ctor::Nil_();
                     },
                     [&](const typename List<T1>::Cons _args)
                         -> std::shared_ptr<List<T1>> {
                       T1 y = _args.d_a0;
                       std::shared_ptr<List<T1>> ys = _args.d_a1;
                       return List<T1>::ctor::Cons_(
                           y, update_nth_frame<T1>(n_, x, std::move(ys)));
                     }},
          l->v());
    }
  }

  using reg_frame = std::shared_ptr<List<unsigned int>>;
  using chip_frame = std::shared_ptr<List<reg_frame>>;
  using bank_frame = std::shared_ptr<List<chip_frame>>;
  __attribute__((pure)) static reg_frame
  upd_main_in_reg_frame(const std::shared_ptr<List<unsigned int>> &rg,
                        const unsigned int i, const unsigned int v);
  __attribute__((pure)) static chip_frame upd_reg_in_chip_frame(
      const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ch,
      const unsigned int r, const std::shared_ptr<List<unsigned int>> &rg);
  __attribute__((pure)) static bank_frame upd_chip_in_bank_frame(
      const std::shared_ptr<
          List<std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>>> &bk,
      const unsigned int c,
      const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ch);
  static inline const bank_frame sample_bank_frame = List<
      std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>>::ctor::
      Cons_(List<std::shared_ptr<List<unsigned int>>>::ctor::Cons_(
                List<unsigned int>::ctor::Cons_(
                    1u, List<unsigned int>::ctor::Cons_(
                            2u, List<unsigned int>::ctor::Cons_(
                                    3u, List<unsigned int>::ctor::Nil_()))),
                List<std::shared_ptr<List<unsigned int>>>::ctor::Cons_(
                    List<unsigned int>::ctor::Cons_(
                        4u, List<unsigned int>::ctor::Cons_(
                                5u, List<unsigned int>::ctor::Cons_(
                                        6u, List<unsigned int>::ctor::Nil_()))),
                    List<std::shared_ptr<List<unsigned int>>>::ctor::Nil_())),
            List<std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>>::
                ctor::Cons_(
                    List<std::shared_ptr<List<unsigned int>>>::ctor::Cons_(
                        List<unsigned int>::ctor::Cons_(
                            7u,
                            List<unsigned int>::ctor::Cons_(
                                8u, List<unsigned int>::ctor::Cons_(
                                        9u, List<unsigned int>::ctor::Nil_()))),
                        List<std::shared_ptr<List<unsigned int>>>::ctor::Cons_(
                            List<unsigned int>::ctor::Cons_(
                                10u,
                                List<unsigned int>::ctor::Cons_(
                                    11u,
                                    List<unsigned int>::ctor::Cons_(
                                        12u,
                                        List<unsigned int>::ctor::Nil_()))),
                            List<std::shared_ptr<List<unsigned int>>>::ctor::
                                Nil_())),
                    List<std::shared_ptr<List<
                        std::shared_ptr<List<unsigned int>>>>>::ctor::Nil_()));
  static inline const bank_frame updated_bank_frame = [](void) {
    std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> ch =
        sample_bank_frame->nth(
            0u, List<std::shared_ptr<List<unsigned int>>>::ctor::Nil_());
    std::shared_ptr<List<unsigned int>> rg =
        std::move(ch)->nth(1u, List<unsigned int>::ctor::Nil_());
    std::shared_ptr<List<unsigned int>> rg_ =
        upd_main_in_reg_frame(std::move(rg), 2u, 99u);
    std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> ch_ =
        upd_reg_in_chip_frame(std::move(ch), 1u, std::move(rg_));
    return upd_chip_in_bank_frame(sample_bank_frame, 0u, std::move(ch_));
  }();
  static inline const bool test_write_frame_different_chip =
      updated_bank_frame
          ->nth(1u, List<std::shared_ptr<List<unsigned int>>>::ctor::Nil_())
          ->nth(0u, List<unsigned int>::ctor::Nil_())
          ->nth(2u, 0u) == 7u;

  template <typename T1>
  static std::shared_ptr<List<T1>>
  update_nth_preserve(const unsigned int n, const T1 x,
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
      return std::visit(
          Overloaded{[](const typename List<T1>::Nil _args)
                         -> std::shared_ptr<List<T1>> {
                       return List<T1>::ctor::Nil_();
                     },
                     [&](const typename List<T1>::Cons _args)
                         -> std::shared_ptr<List<T1>> {
                       T1 y = _args.d_a0;
                       std::shared_ptr<List<T1>> ys = _args.d_a1;
                       return List<T1>::ctor::Cons_(
                           y, update_nth_preserve<T1>(n_, x, std::move(ys)));
                     }},
          l->v());
    }
  }

  struct state_preserve {
    std::shared_ptr<List<unsigned int>> ram_sys_preserve;
    unsigned int cur_bank_preserve;
  };

  static std::shared_ptr<List<unsigned int>>
  ram_write_main_sys_preserve(const std::shared_ptr<state_preserve> &s,
                              const unsigned int v);
  static std::shared_ptr<state_preserve>
  execute_write(std::shared_ptr<state_preserve> s, const unsigned int v);
  static inline const std::shared_ptr<state_preserve> sample_preserve =
      std::make_shared<state_preserve>(state_preserve{
          List<unsigned int>::ctor::Cons_(
              10u,
              List<unsigned int>::ctor::Cons_(
                  20u, List<unsigned int>::ctor::Cons_(
                           30u, List<unsigned int>::ctor::Cons_(
                                    40u, List<unsigned int>::ctor::Nil_())))),
          1u});
  static inline const bool test_write_main_preserves_other_bank =
      execute_write(sample_preserve, 99u)->ram_sys_preserve->nth(3u, 0u) == 40u;
  __attribute__((pure)) static bool
  ram_addr_disjointb(const unsigned int b1, const unsigned int c1,
                     const unsigned int r1, const unsigned int i1,
                     const unsigned int b2, const unsigned int c2,
                     const unsigned int r2, const unsigned int i2);
  static inline const unsigned int test_addr_disjoint_bool =
      ([](void) {
        if (ram_addr_disjointb(0u, 1u, 2u, 3u, 0u, 1u, 2u, 3u)) {
          return 1u;
        } else {
          return 0u;
        }
      }() +
       [](void) {
         if (ram_addr_disjointb(0u, 1u, 2u, 3u, 0u, 1u, 2u, 4u)) {
           return 1u;
         } else {
           return 0u;
         }
       }());

  struct reg_nested_bank {
    std::shared_ptr<List<unsigned int>> status_;
  };

  struct chip_nested_bank {
    std::shared_ptr<List<std::shared_ptr<reg_nested_bank>>> regs_;
  };

  struct bank_nested_bank {
    std::shared_ptr<List<std::shared_ptr<chip_nested_bank>>> chips_;
  };

  struct state_nested_bank {
    std::shared_ptr<List<std::shared_ptr<bank_nested_bank>>> banks_;
  };

  template <typename T1>
  static std::shared_ptr<List<T1>>
  update_nth_nested_bank(const unsigned int n, const T1 x,
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
      return std::visit(
          Overloaded{[](const typename List<T1>::Nil _args)
                         -> std::shared_ptr<List<T1>> {
                       return List<T1>::ctor::Nil_();
                     },
                     [&](const typename List<T1>::Cons _args)
                         -> std::shared_ptr<List<T1>> {
                       T1 y = _args.d_a0;
                       std::shared_ptr<List<T1>> ys = _args.d_a1;
                       return List<T1>::ctor::Cons_(
                           y, update_nth_nested_bank<T1>(n_, x, std::move(ys)));
                     }},
          l->v());
    }
  }

  static std::shared_ptr<bank_nested_bank>
  get_bank0(const std::shared_ptr<state_nested_bank> &s);
  static std::shared_ptr<chip_nested_bank>
  get_chip0(const std::shared_ptr<bank_nested_bank> &b);
  static std::shared_ptr<reg_nested_bank>
  get_reg0(const std::shared_ptr<chip_nested_bank> &c);
  static std::shared_ptr<state_nested_bank>
  write_status0(std::shared_ptr<state_nested_bank> s, const unsigned int v);
  __attribute__((pure)) static unsigned int
  read_status0(const std::shared_ptr<state_nested_bank> &s);
  static inline const std::shared_ptr<state_nested_bank> sample_nested_bank =
      std::make_shared<state_nested_bank>(state_nested_bank{
          List<std::shared_ptr<bank_nested_bank>>::ctor::Cons_(
              std::make_shared<bank_nested_bank>(bank_nested_bank{
                  List<std::shared_ptr<chip_nested_bank>>::ctor::Cons_(
                      std::make_shared<chip_nested_bank>(chip_nested_bank{
                          List<std::shared_ptr<reg_nested_bank>>::ctor::Cons_(
                              std::make_shared<reg_nested_bank>(reg_nested_bank{
                                  List<unsigned int>::ctor::Cons_(
                                      3u,
                                      List<unsigned int>::ctor::Cons_(
                                          4u,
                                          List<unsigned int>::ctor::Nil_()))}),
                              List<std::shared_ptr<reg_nested_bank>>::ctor::
                                  Nil_())}),
                      List<std::shared_ptr<chip_nested_bank>>::ctor::Nil_())}),
              List<std::shared_ptr<bank_nested_bank>>::ctor::Nil_())});
  static inline const unsigned int test_nested_bank_status_write =
      read_status0(write_status0(sample_nested_bank, 7u));
  enum class Item { e_S_, e_S_0 };

  template <typename T1>
  static T1 item_rect(const T1 f, const T1 f0, const Item i) {
    return [&](void) {
      switch (i) {
      case Item::e_S_: {
        return f;
      }
      case Item::e_S_0: {
        return f0;
      }
      }
    }();
  }

  template <typename T1>
  static T1 item_rec(const T1 f, const T1 f0, const Item i) {
    return [&](void) {
      switch (i) {
      case Item::e_S_: {
        return f;
      }
      case Item::e_S_0: {
        return f0;
      }
      }
    }();
  }

  __attribute__((pure)) static unsigned int score(const Item x);
  static inline const unsigned int test_accessor_namespace =
      (score(Item::e_S_) + score(Item::e_S_0));

  static inline const std::pair<
      std::pair<
          std::pair<
              std::pair<
                  std::pair<
                      std::pair<std::pair<std::pair<std::pair<unsigned int,
                                                              unsigned int>,
                                                    unsigned int>,
                                          unsigned int>,
                                unsigned int>,
                      unsigned int>,
                  bool>,
              bool>,
          unsigned int>,
      unsigned int>
      t = std::make_pair(
          std::make_pair(
              std::make_pair(
                  std::make_pair(
                      std::make_pair(
                          std::make_pair(
                              std::make_pair(
                                  std::make_pair(
                                      std::make_pair(test_main_write_chain,
                                                     test_port_write_chain),
                                      test_status_write_chain),
                                  test_read_main_selector),
                              test_read_nested),
                          test_addr_disjoint_bool),
                      test_write_frame_different_chip),
                  test_write_main_preserves_other_bank),
              test_nested_bank_status_write),
          test_accessor_namespace);
};

#endif // INCLUDED_RAM_OPS
