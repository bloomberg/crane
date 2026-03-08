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
  unsigned int length() const {
    return std::visit(
        Overloaded{[](const typename List<A>::nil _args) -> unsigned int {
                     return 0u;
                   },
                   [](const typename List<A>::cons _args) -> unsigned int {
                     std::shared_ptr<List<A>> l_ = _args._a1;
                     return (std::move(l_)->length() + 1);
                   }},
        this->v());
  }
};

struct SetPromThenWpm {
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

  struct state {
    std::shared_ptr<List<unsigned int>> regs;
    std::shared_ptr<List<unsigned int>> rom;
    unsigned int acc;
    unsigned int pc;
    std::shared_ptr<List<unsigned int>> stack;
    unsigned int cur_bank;
    std::shared_ptr<List<unsigned int>> rom_ports;
    unsigned int sel_rom;
    unsigned int prom_addr;
    unsigned int prom_data;
    bool prom_enable;
  };

  static std::shared_ptr<state> set_prom_params(std::shared_ptr<state> s,
                                                const unsigned int addr,
                                                const unsigned int data,
                                                const bool enable);

  static std::shared_ptr<state> execute_wpm(std::shared_ptr<state> s);

  static inline const std::shared_ptr<state> sample =
      std::make_shared<state>(state{
          List<unsigned int>::ctor::cons_(
              1u, List<unsigned int>::ctor::cons_(
                      2u, List<unsigned int>::ctor::cons_(
                              3u, List<unsigned int>::ctor::cons_(
                                      4u, List<unsigned int>::ctor::nil_())))),
          List<unsigned int>::ctor::cons_(
              10u,
              List<unsigned int>::ctor::cons_(
                  11u,
                  List<unsigned int>::ctor::cons_(
                      12u,
                      List<unsigned int>::ctor::cons_(
                          13u,
                          List<unsigned int>::ctor::cons_(
                              14u,
                              List<unsigned int>::ctor::cons_(
                                  15u,
                                  List<unsigned int>::ctor::cons_(
                                      16u, List<unsigned int>::ctor::cons_(
                                               17u, List<unsigned int>::ctor::
                                                        nil_())))))))),
          7u, 1025u,
          List<unsigned int>::ctor::cons_(
              7u, List<unsigned int>::ctor::cons_(
                      9u, List<unsigned int>::ctor::nil_())),
          2u,
          List<unsigned int>::ctor::cons_(
              3u, List<unsigned int>::ctor::cons_(
                      4u, List<unsigned int>::ctor::cons_(
                              5u, List<unsigned int>::ctor::cons_(
                                      6u, List<unsigned int>::ctor::nil_())))),
          5u, 0u, 0u, false});

  static inline const bool check_pc_bound = [](void) {
    std::shared_ptr<state> after =
        execute_wpm(set_prom_params(sample, 3u, 99u, true));
    return (std::move(after)->pc < 4096u);
  }();

  static inline const bool check_acc_bound = [](void) {
    std::shared_ptr<state> after =
        execute_wpm(set_prom_params(sample, 3u, 99u, true));
    return (std::move(after)->acc < 16u);
  }();

  static inline const bool check_bank_bound = [](void) {
    std::shared_ptr<state> after =
        execute_wpm(set_prom_params(sample, 3u, 99u, true));
    return (std::move(after)->cur_bank < 8u);
  }();

  static inline const bool check_regs_length = [](void) {
    std::shared_ptr<state> after =
        execute_wpm(set_prom_params(sample, 3u, 99u, true));
    return (std::move(after)->regs->length() == 4u);
  }();

  static inline const bool check_rom_ports_length = [](void) {
    std::shared_ptr<state> after =
        execute_wpm(set_prom_params(sample, 3u, 99u, true));
    return (std::move(after)->rom_ports->length() == 4u);
  }();

  static inline const bool check_sel_rom_bound = [](void) {
    std::shared_ptr<state> after =
        execute_wpm(set_prom_params(sample, 3u, 99u, true));
    return (std::move(after)->sel_rom < 16u);
  }();

  static inline const bool check_stack_length = [](void) {
    std::shared_ptr<state> after =
        execute_wpm(set_prom_params(sample, 3u, 99u, true));
    return (std::move(after)->stack->length() <= 3u);
  }();

  static inline const bool check_prom_addr_bound = [](void) {
    std::shared_ptr<state> after =
        execute_wpm(set_prom_params(sample, 2048u, 99u, true));
    return (std::move(after)->prom_addr < 4096u);
  }();

  static inline const bool check_prom_data_bound = [](void) {
    std::shared_ptr<state> after =
        execute_wpm(set_prom_params(sample, 3u, 155u, true));
    return (std::move(after)->prom_data < 256u);
  }();

  static inline const bool check_rom_length = [](void) {
    std::shared_ptr<state> after =
        execute_wpm(set_prom_params(sample, 3u, 99u, true));
    return (std::move(after)->rom->length() == 8u);
  }();

  static inline const bool t =
      (((((((((check_pc_bound && check_acc_bound) && check_bank_bound) &&
             check_regs_length) &&
            check_rom_ports_length) &&
           check_sel_rom_bound) &&
          check_stack_length) &&
         check_prom_addr_bound) &&
        check_prom_data_bound) &&
       check_rom_length);
};
