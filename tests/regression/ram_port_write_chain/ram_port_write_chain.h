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

struct RamPortWriteChain {
  struct chip {
    unsigned int chip_port;
  };

  static unsigned int chip_port(const std::shared_ptr<chip> &c);

  struct bank {
    std::shared_ptr<List<std::shared_ptr<chip>>> bank_chips;
  };

  static std::shared_ptr<List<std::shared_ptr<chip>>>
  bank_chips(const std::shared_ptr<bank> &b);

  struct state {
    std::shared_ptr<List<std::shared_ptr<bank>>> ram_sys;
    unsigned int cur_bank;
    unsigned int sel_chip;
  };

  static std::shared_ptr<List<std::shared_ptr<bank>>>
  ram_sys(const std::shared_ptr<state> &s);

  static unsigned int cur_bank(const std::shared_ptr<state> &s);

  static unsigned int sel_chip(const std::shared_ptr<state> &s);

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

  static std::shared_ptr<bank> get_bank(const std::shared_ptr<state> &s,
                                        const unsigned int b);

  static std::shared_ptr<chip> get_chip(const std::shared_ptr<bank> &bk,
                                        const unsigned int c);

  static std::shared_ptr<chip> upd_port_in_chip(const std::shared_ptr<chip> &_x,
                                                const unsigned int v);

  static std::shared_ptr<bank> upd_chip_in_bank(std::shared_ptr<bank> bk,
                                                const unsigned int c,
                                                std::shared_ptr<chip> ch);

  static std::shared_ptr<List<std::shared_ptr<bank>>>
  upd_bank_in_sys(const std::shared_ptr<state> &s, const unsigned int b,
                  const std::shared_ptr<bank> &bk);

  static std::shared_ptr<List<std::shared_ptr<bank>>>
  ram_write_port_sys(const std::shared_ptr<state> &s, const unsigned int v);

  static inline const unsigned int t = [](void) {
    std::shared_ptr<chip> ch0 = std::make_shared<chip>(chip{0});
    std::shared_ptr<bank> bk0 =
        std::make_shared<bank>(bank{List<std::shared_ptr<chip>>::ctor::cons_(
            std::move(ch0), List<std::shared_ptr<chip>>::ctor::nil_())});
    std::unique_ptr<state> s = std::make_unique<state>(
        state{List<std::shared_ptr<bank>>::ctor::cons_(
                  std::move(bk0), List<std::shared_ptr<bank>>::ctor::nil_()),
              0, 0});
    std::shared_ptr<List<std::shared_ptr<bank>>> sys_ = ram_write_port_sys(
        std::move(s),
        (((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
               1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1));
    std::shared_ptr<bank> bk_ = std::move(sys_)->nth(
        0, std::make_shared<bank>(
               bank{List<std::shared_ptr<chip>>::ctor::nil_()}));
    std::shared_ptr<chip> ch_ =
        std::move(bk_)->bank_chips->nth(0, std::make_shared<chip>(chip{0}));
    return std::move(ch_)->chip_port;
  }();
};
