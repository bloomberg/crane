#ifndef INCLUDED_WPM_OPS
#define INCLUDED_WPM_OPS

#include <memory>
#include <type_traits>
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

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  t_A nth(const unsigned int n, const t_A default0) const {
    if (n <= 0) {
      if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
        return default0;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<t_A>::Cons>(this->v());
        return d_a0;
      }
    } else {
      unsigned int m = n - 1;
      if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
        return default0;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<t_A>::Cons>(this->v());
        return d_a10->nth(m, default0);
      }
    }
  }
};

struct WpmOps {
  template <typename T1>
  static std::shared_ptr<List<T1>>
  update_nth(const unsigned int n, const T1 x,
             const std::shared_ptr<List<T1>> &l) {
    if (n <= 0) {
      if (std::holds_alternative<typename List<T1>::Nil>(l->v())) {
        return List<T1>::nil();
      } else {
        const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l->v());
        return List<T1>::cons(x, d_a1);
      }
    } else {
      unsigned int n_ = n - 1;
      if (std::holds_alternative<typename List<T1>::Nil>(l->v())) {
        return List<T1>::nil();
      } else {
        const auto &[d_a00, d_a10] = std::get<typename List<T1>::Cons>(l->v());
        return List<T1>::cons(d_a00, update_nth<T1>(n_, x, d_a10));
      }
    }
  }

  __attribute__((pure)) static bool
  nat_list_eqb(const std::shared_ptr<List<unsigned int>> &xs,
               const std::shared_ptr<List<unsigned int>> &ys);

  struct state1 {
    std::shared_ptr<List<unsigned int>> rom1;
    unsigned int prom_addr1;
    unsigned int prom_data1;
    bool prom_enable1;
  };

  static std::shared_ptr<state1> execute_wpm1(const std::shared_ptr<state1> &s);
  static inline const std::shared_ptr<state1> sample1 =
      std::make_shared<state1>(state1{
          List<unsigned int>::cons(
              10u, List<unsigned int>::cons(
                       11u, List<unsigned int>::cons(
                                12u, List<unsigned int>::cons(
                                         13u, List<unsigned int>::nil())))),
          2u, 99u, false});
  static inline const std::shared_ptr<state1> after1 = execute_wpm1(sample1);
  static inline const bool test_wpm_disabled_is_nop =
      (after1->rom1->nth(0u, 0u) == 10u &&
       (after1->rom1->nth(1u, 0u) == 11u &&
        (after1->rom1->nth(2u, 0u) == 12u &&
         after1->rom1->nth(3u, 0u) == 13u)));

  struct state2 {
    std::shared_ptr<List<unsigned int>> ram_sys2;
    std::shared_ptr<List<unsigned int>> rom2;
    unsigned int prom_addr2;
    unsigned int prom_data2;
    bool prom_enable2;
  };

  static std::shared_ptr<state2> execute_wpm2(const std::shared_ptr<state2> &s);
  static inline const std::shared_ptr<state2> sample2 =
      std::make_shared<state2>(state2{
          List<unsigned int>::cons(
              5u,
              List<unsigned int>::cons(
                  6u, List<unsigned int>::cons(7u, List<unsigned int>::nil()))),
          List<unsigned int>::cons(
              10u, List<unsigned int>::cons(
                       11u, List<unsigned int>::cons(
                                12u, List<unsigned int>::nil()))),
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

  static std::shared_ptr<state3> execute_wpm3(const std::shared_ptr<state3> &s);
  static inline const std::shared_ptr<state3> sample3 =
      std::make_shared<state3>(state3{
          List<unsigned int>::cons(
              1u,
              List<unsigned int>::cons(
                  2u, List<unsigned int>::cons(3u, List<unsigned int>::nil()))),
          List<unsigned int>::cons(
              10u, List<unsigned int>::cons(
                       11u, List<unsigned int>::cons(
                                12u, List<unsigned int>::nil()))),
          1u, 99u, true});
  static inline const bool test_wpm_enabled_preserves_regs =
      nat_list_eqb(execute_wpm3(sample3)->regs3, sample3->regs3);

  struct state4 {
    std::shared_ptr<List<unsigned int>> rom4;
    unsigned int prom_addr4;
    unsigned int prom_data4;
    bool prom_enable4;
  };

  static std::shared_ptr<state4> execute_wpm4(const std::shared_ptr<state4> &s);
  static inline const unsigned int test_wpm_update_gate = []() {
    std::shared_ptr<state4> s = std::make_shared<state4>(state4{
        List<unsigned int>::cons(
            10u,
            List<unsigned int>::cons(
                11u, List<unsigned int>::cons(12u, List<unsigned int>::nil()))),
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

  static std::shared_ptr<state5> execute_wpm5(const std::shared_ptr<state5> &s);
  static inline const std::shared_ptr<state5> sample5 =
      std::make_shared<state5>(state5{
          List<unsigned int>::cons(
              10u, List<unsigned int>::cons(
                       11u, List<unsigned int>::cons(
                                12u, List<unsigned int>::cons(
                                         13u, List<unsigned int>::nil())))),
          2u, 99u, true});
  static inline const bool test_wpm_updates_rom_at_addr =
      execute_wpm5(sample5)->rom5->nth(2u, 0u) == 99u;

  struct state6 {
    std::shared_ptr<List<unsigned int>> rom6;
    unsigned int prom_addr6;
    unsigned int prom_data6;
    bool prom_enable6;
  };

  static std::shared_ptr<state6> execute_wpm6(const std::shared_ptr<state6> &s);
  static inline const std::shared_ptr<state6> sample6 =
      std::make_shared<state6>(state6{
          List<unsigned int>::cons(
              10u, List<unsigned int>::cons(
                       11u, List<unsigned int>::cons(
                                12u, List<unsigned int>::cons(
                                         13u, List<unsigned int>::nil())))),
          2u, 99u, true});
  static inline const std::shared_ptr<state6> after6 = execute_wpm6(sample6);
  static inline const bool test_wpm_writes_exactly_once =
      (after6->rom6->nth(2u, 0u) == 99u &&
       (after6->rom6->nth(0u, 0u) == 10u &&
        (after6->rom6->nth(1u, 0u) == 11u &&
         after6->rom6->nth(3u, 0u) == 13u)));
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

#endif // INCLUDED_WPM_OPS
