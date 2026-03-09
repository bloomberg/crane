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

struct WpmOps {
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

  static bool nat_list_eqb(const std::shared_ptr<List<unsigned int>> &xs,
                           const std::shared_ptr<List<unsigned int>> &ys);

  struct state1 {
    std::shared_ptr<List<unsigned int>> rom1;
    unsigned int prom_addr1;
    unsigned int prom_data1;
    bool prom_enable1;
  };

  static std::shared_ptr<state1> execute_wpm1(std::shared_ptr<state1> s);

  static inline const std::shared_ptr<state1> sample1 =
      std::make_shared<state1>(state1{
          List<unsigned int>::ctor::cons_(
              10u,
              List<unsigned int>::ctor::cons_(
                  11u, List<unsigned int>::ctor::cons_(
                           12u, List<unsigned int>::ctor::cons_(
                                    13u, List<unsigned int>::ctor::nil_())))),
          2u, 99u, false});

  static inline const std::shared_ptr<state1> after1 = execute_wpm1(sample1);

  static inline const bool test_wpm_disabled_is_nop =
      ((after1->rom1->nth(0u, 0u) == 10u) &&
       ((after1->rom1->nth(1u, 0u) == 11u) &&
        ((after1->rom1->nth(2u, 0u) == 12u) &&
         (after1->rom1->nth(3u, 0u) == 13u))));

  struct state2 {
    std::shared_ptr<List<unsigned int>> ram_sys2;
    std::shared_ptr<List<unsigned int>> rom2;
    unsigned int prom_addr2;
    unsigned int prom_data2;
    bool prom_enable2;
  };

  static std::shared_ptr<state2> execute_wpm2(std::shared_ptr<state2> s);

  static inline const std::shared_ptr<state2> sample2 =
      std::make_shared<state2>(
          state2{List<unsigned int>::ctor::cons_(
                     5u, List<unsigned int>::ctor::cons_(
                             6u, List<unsigned int>::ctor::cons_(
                                     7u, List<unsigned int>::ctor::nil_()))),
                 List<unsigned int>::ctor::cons_(
                     10u, List<unsigned int>::ctor::cons_(
                              11u, List<unsigned int>::ctor::cons_(
                                       12u, List<unsigned int>::ctor::nil_()))),
                 1u, 99u, true});

  static inline const bool test_wpm_enabled_preserves_ram =
      nat_list_eqb(execute_wpm2(sample2)->ram_sys2, sample2->ram_sys2);

  struct state3 {
    std::shared_ptr<List<unsigned int>> regs3;
    std::shared_ptr<List<unsigned int>> rom3;
    unsigned int prom_addr3;
    unsigned int prom_data3;
    bool prom_enable3;
  };

  static std::shared_ptr<state3> execute_wpm3(std::shared_ptr<state3> s);

  static inline const std::shared_ptr<state3> sample3 =
      std::make_shared<state3>(
          state3{List<unsigned int>::ctor::cons_(
                     1u, List<unsigned int>::ctor::cons_(
                             2u, List<unsigned int>::ctor::cons_(
                                     3u, List<unsigned int>::ctor::nil_()))),
                 List<unsigned int>::ctor::cons_(
                     10u, List<unsigned int>::ctor::cons_(
                              11u, List<unsigned int>::ctor::cons_(
                                       12u, List<unsigned int>::ctor::nil_()))),
                 1u, 99u, true});

  static inline const bool test_wpm_enabled_preserves_regs =
      nat_list_eqb(execute_wpm3(sample3)->regs3, sample3->regs3);

  struct state4 {
    std::shared_ptr<List<unsigned int>> rom4;
    unsigned int prom_addr4;
    unsigned int prom_data4;
    bool prom_enable4;
  };

  static std::shared_ptr<state4> execute_wpm4(std::shared_ptr<state4> s);

  static inline const unsigned int test_wpm_update_gate = [](void) {
    std::unique_ptr<state4> s = std::make_unique<state4>(
        state4{List<unsigned int>::ctor::cons_(
                   10u, List<unsigned int>::ctor::cons_(
                            11u, List<unsigned int>::ctor::cons_(
                                     12u, List<unsigned int>::ctor::nil_()))),
               1u, 99u, true});
    std::shared_ptr<state4> s_ = execute_wpm4(std::move(s));
    return std::move(s_)->rom4->nth(1u, 0u);
  }();

  struct state5 {
    std::shared_ptr<List<unsigned int>> rom5;
    unsigned int prom_addr5;
    unsigned int prom_data5;
    bool prom_enable5;
  };

  static std::shared_ptr<state5> execute_wpm5(std::shared_ptr<state5> s);

  static inline const std::shared_ptr<state5> sample5 =
      std::make_shared<state5>(state5{
          List<unsigned int>::ctor::cons_(
              10u,
              List<unsigned int>::ctor::cons_(
                  11u, List<unsigned int>::ctor::cons_(
                           12u, List<unsigned int>::ctor::cons_(
                                    13u, List<unsigned int>::ctor::nil_())))),
          2u, 99u, true});

  static inline const bool test_wpm_updates_rom_at_addr =
      (execute_wpm5(sample5)->rom5->nth(2u, 0u) == 99u);

  struct state6 {
    std::shared_ptr<List<unsigned int>> rom6;
    unsigned int prom_addr6;
    unsigned int prom_data6;
    bool prom_enable6;
  };

  static std::shared_ptr<state6> execute_wpm6(std::shared_ptr<state6> s);

  static inline const std::shared_ptr<state6> sample6 =
      std::make_shared<state6>(state6{
          List<unsigned int>::ctor::cons_(
              10u,
              List<unsigned int>::ctor::cons_(
                  11u, List<unsigned int>::ctor::cons_(
                           12u, List<unsigned int>::ctor::cons_(
                                    13u, List<unsigned int>::ctor::nil_())))),
          2u, 99u, true});

  static inline const std::shared_ptr<state6> after6 = execute_wpm6(sample6);

  static inline const bool test_wpm_writes_exactly_once =
      ((after6->rom6->nth(2u, 0u) == 99u) &&
       ((after6->rom6->nth(0u, 0u) == 10u) &&
        ((after6->rom6->nth(1u, 0u) == 11u) &&
         (after6->rom6->nth(3u, 0u) == 13u))));

  static inline const std::pair<
      std::pair<std::pair<std::pair<std::pair<bool, bool>, bool>, unsigned int>,
                bool>,
      bool>
      t = std::make_pair(
          std::make_pair(
              std::make_pair(
                  std::make_pair(std::make_pair(test_wpm_disabled_is_nop,
                                                test_wpm_enabled_preserves_ram),
                                 test_wpm_enabled_preserves_regs),
                  test_wpm_update_gate),
              test_wpm_updates_rom_at_addr),
          test_wpm_writes_exactly_once);
};
