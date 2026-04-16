#ifndef INCLUDED_PROM_OPS
#define INCLUDED_PROM_OPS

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

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

  __attribute__((pure)) unsigned int length() const {
    if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(this->v());
      return (d_a1->length() + 1);
    }
  }
};

struct ListDef {
  template <typename T1>
  static T1 nth(const unsigned int n, const std::shared_ptr<List<T1>> &l,
                const T1 default0);
};

struct Bool {
  __attribute__((pure)) static bool eqb(const bool b1, const bool b2);
};

struct PromOps {
  __attribute__((pure)) static bool
  nat_list_eqb(const std::shared_ptr<List<unsigned int>> &xs,
               const std::shared_ptr<List<unsigned int>> &ys);

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

  struct state1 {
    unsigned int prom_data1;
    bool prom_enable1;
  };

  __attribute__((pure)) static unsigned int
  prom_data_or_zero(const std::shared_ptr<state1> &s);
  static inline const unsigned int test1 =
      prom_data_or_zero(std::make_shared<state1>(state1{77u, false}));

  struct state2 {
    unsigned int acc2;
    unsigned int prom_addr2;
    unsigned int prom_data2;
    bool prom_enable2;
  };

  __attribute__((pure)) static unsigned int
  flagged_sum(const std::shared_ptr<state2> &s);
  static inline const unsigned int test2 =
      flagged_sum(std::make_shared<state2>(state2{3u, 12u, 77u, false}));

  struct state3 {
    unsigned int acc3;
    std::shared_ptr<List<unsigned int>> regs3;
    bool carry3;
    unsigned int pc3;
    std::shared_ptr<List<unsigned int>> stack3;
    std::shared_ptr<List<unsigned int>> ram_sys3;
    unsigned int cur_bank3;
    unsigned int sel_ram3;
    std::shared_ptr<List<unsigned int>> rom_ports3;
    unsigned int sel_rom3;
    std::shared_ptr<List<unsigned int>> rom3;
    bool test_pin3;
    unsigned int prom_addr3;
    unsigned int prom_data3;
    bool prom_enable3;
  };

  static std::shared_ptr<state3>
  set_prom_params3(const std::shared_ptr<state3> &s, const unsigned int addr,
                   const unsigned int data, const bool enable);
  static inline const unsigned int test3 = []() {
    return []() {
      std::shared_ptr<state3> s = std::make_shared<state3>(state3{
          1u,
          List<unsigned int>::cons(
              2u, List<unsigned int>::cons(3u, List<unsigned int>::nil())),
          false, 4u, List<unsigned int>::cons(5u, List<unsigned int>::nil()),
          List<unsigned int>::cons(6u, List<unsigned int>::nil()), 0u, 0u,
          List<unsigned int>::cons(7u, List<unsigned int>::nil()), 0u,
          List<unsigned int>::cons(
              8u, List<unsigned int>::cons(9u, List<unsigned int>::nil())),
          true, 0u, 0u, false});
      std::shared_ptr<state3> s_ =
          set_prom_params3(std::move(s), 21u, 144u, true);
      return ((s_->prom_addr3 + [&]() -> unsigned int {
                if (s_->prom_enable3) {
                  return std::move(s_)->prom_data3;
                } else {
                  return 0u;
                }
              }()) +
              s_->regs3->length());
    }();
  }();
  static inline const unsigned int test4 = []() {
    return []() {
      std::shared_ptr<state3> s = std::make_shared<state3>(state3{
          1u,
          List<unsigned int>::cons(
              2u, List<unsigned int>::cons(3u, List<unsigned int>::nil())),
          false, 4u, List<unsigned int>::cons(5u, List<unsigned int>::nil()),
          List<unsigned int>::cons(6u, List<unsigned int>::nil()), 0u, 0u,
          List<unsigned int>::cons(7u, List<unsigned int>::nil()), 0u,
          List<unsigned int>::cons(
              8u, List<unsigned int>::cons(9u, List<unsigned int>::nil())),
          true, 0u, 0u, false});
      std::shared_ptr<state3> s_ =
          set_prom_params3(std::move(s), 21u, 144u, true);
      return ((s_->prom_addr3 + [&]() -> unsigned int {
                if (s_->prom_enable3) {
                  return std::move(s_)->prom_data3;
                } else {
                  return 0u;
                }
              }()) +
              s_->regs3->length());
    }();
  }();

  struct state5 {
    unsigned int acc5;
    std::shared_ptr<List<unsigned int>> regs5;
    std::shared_ptr<List<unsigned int>> rom5;
    unsigned int prom_addr5;
    unsigned int prom_data5;
    bool prom_enable5;
  };

  static std::shared_ptr<state5>
  set_prom_params5(const std::shared_ptr<state5> &s, const unsigned int addr,
                   const unsigned int data, const bool enable);
  static inline const unsigned int test5 = []() {
    return []() {
      std::shared_ptr<state5> s = std::make_shared<state5>(state5{
          3u,
          List<unsigned int>::cons(
              1u, List<unsigned int>::cons(2u, List<unsigned int>::nil())),
          List<unsigned int>::cons(
              9u,
              List<unsigned int>::cons(
                  8u, List<unsigned int>::cons(7u, List<unsigned int>::nil()))),
          0u, 0u, false});
      std::shared_ptr<state5> s_ =
          set_prom_params5(std::move(s), 23u, 77u, true);
      return ((s_->acc5 + s_->prom_addr5) + [&]() -> unsigned int {
        if (s_->prom_enable5) {
          return std::move(s_)->prom_data5;
        } else {
          return 0u;
        }
      }());
    }();
  }();

  struct state6 {
    std::shared_ptr<List<unsigned int>> rom6;
    unsigned int prom_addr6;
    unsigned int prom_data6;
    bool prom_enable6;
  };

  static std::shared_ptr<state6>
  set_prom_params6(const std::shared_ptr<state6> &s, const unsigned int addr,
                   const unsigned int data, const bool enable);
  static inline const std::shared_ptr<state6> sample6 =
      std::make_shared<state6>(state6{
          List<unsigned int>::cons(
              10u, List<unsigned int>::cons(
                       11u, List<unsigned int>::cons(
                                12u, List<unsigned int>::cons(
                                         13u, List<unsigned int>::nil())))),
          0u, 0u, false});
  static inline const bool test6 =
      Bool::eqb(set_prom_params6(sample6, 2u, 99u, true)->prom_enable6, true);

  struct state7 {
    std::shared_ptr<List<unsigned int>> regs7;
    std::shared_ptr<List<unsigned int>> ram_sys7;
    unsigned int prom_addr7;
    unsigned int prom_data7;
    bool prom_enable7;
  };

  static std::shared_ptr<state7>
  set_prom_params7(const std::shared_ptr<state7> &s, const unsigned int addr,
                   const unsigned int data, const bool enable);
  static inline const std::shared_ptr<state7> sample7 =
      std::make_shared<state7>(state7{
          List<unsigned int>::cons(
              1u,
              List<unsigned int>::cons(
                  2u, List<unsigned int>::cons(3u, List<unsigned int>::nil()))),
          List<unsigned int>::cons(
              9u,
              List<unsigned int>::cons(
                  8u, List<unsigned int>::cons(7u, List<unsigned int>::nil()))),
          0u, 0u, false});
  static inline const bool test7 = nat_list_eqb(
      set_prom_params7(sample7, 12u, 99u, true)->ram_sys7, sample7->ram_sys7);

  struct state8 {
    std::shared_ptr<List<unsigned int>> regs8;
    std::shared_ptr<List<unsigned int>> ram_sys8;
    unsigned int prom_addr8;
    unsigned int prom_data8;
    bool prom_enable8;
  };

  static std::shared_ptr<state8>
  set_prom_params8(const std::shared_ptr<state8> &s, const unsigned int addr,
                   const unsigned int data, const bool enable);
  static inline const std::shared_ptr<state8> sample8 =
      std::make_shared<state8>(state8{
          List<unsigned int>::cons(
              1u,
              List<unsigned int>::cons(
                  2u, List<unsigned int>::cons(3u, List<unsigned int>::nil()))),
          List<unsigned int>::cons(
              9u, List<unsigned int>::cons(8u, List<unsigned int>::nil())),
          0u, 0u, false});
  static inline const bool test8 = nat_list_eqb(
      set_prom_params8(sample8, 12u, 99u, true)->regs8, sample8->regs8);

  struct state9 {
    std::shared_ptr<List<unsigned int>> rom9;
    unsigned int prom_addr9;
    unsigned int prom_data9;
    bool prom_enable9;
  };

  static std::shared_ptr<state9>
  set_prom_params9(const std::shared_ptr<state9> &s, const unsigned int addr,
                   const unsigned int data, const bool enable);
  static inline const std::shared_ptr<state9> sample9 =
      std::make_shared<state9>(state9{
          List<unsigned int>::cons(
              10u, List<unsigned int>::cons(
                       11u, List<unsigned int>::cons(
                                12u, List<unsigned int>::cons(
                                         13u, List<unsigned int>::nil())))),
          0u, 0u, false});
  static inline const bool test9 =
      set_prom_params9(sample9, 12u, 99u, true)->rom9->length() ==
      sample9->rom9->length();

  struct state10 {
    std::shared_ptr<List<unsigned int>> regs10;
    std::shared_ptr<List<unsigned int>> rom10;
    unsigned int acc10;
    unsigned int pc10;
    std::shared_ptr<List<unsigned int>> stack10;
    unsigned int cur_bank10;
    std::shared_ptr<List<unsigned int>> rom_ports10;
    unsigned int sel_rom10;
    unsigned int prom_addr10;
    unsigned int prom_data10;
    bool prom_enable10;
  };

  static std::shared_ptr<state10>
  set_prom_params10(const std::shared_ptr<state10> &s, const unsigned int addr,
                    const unsigned int data, const bool enable);
  static std::shared_ptr<state10>
  execute_wpm10(const std::shared_ptr<state10> &s);
  static inline const std::shared_ptr<state10> sample10 =
      std::make_shared<state10>(state10{
          List<unsigned int>::cons(
              1u, List<unsigned int>::cons(
                      2u, List<unsigned int>::cons(
                              3u, List<unsigned int>::cons(
                                      4u, List<unsigned int>::nil())))),
          List<unsigned int>::cons(
              10u,
              List<unsigned int>::cons(
                  11u,
                  List<unsigned int>::cons(
                      12u,
                      List<unsigned int>::cons(
                          13u,
                          List<unsigned int>::cons(
                              14u,
                              List<unsigned int>::cons(
                                  15u,
                                  List<unsigned int>::cons(
                                      16u,
                                      List<unsigned int>::cons(
                                          17u,
                                          List<unsigned int>::nil())))))))),
          7u, 1025u,
          List<unsigned int>::cons(
              7u, List<unsigned int>::cons(9u, List<unsigned int>::nil())),
          2u,
          List<unsigned int>::cons(
              3u, List<unsigned int>::cons(
                      4u, List<unsigned int>::cons(
                              5u, List<unsigned int>::cons(
                                      6u, List<unsigned int>::nil())))),
          5u, 0u, 0u, false});
  static inline const bool check_pc_bound = []() {
    std::shared_ptr<state10> after =
        execute_wpm10(set_prom_params10(sample10, 3u, 99u, true));
    return std::move(after)->pc10 < 4096u;
  }();
  static inline const bool check_acc_bound = []() {
    std::shared_ptr<state10> after =
        execute_wpm10(set_prom_params10(sample10, 3u, 99u, true));
    return std::move(after)->acc10 < 16u;
  }();
  static inline const bool check_bank_bound = []() {
    std::shared_ptr<state10> after =
        execute_wpm10(set_prom_params10(sample10, 3u, 99u, true));
    return std::move(after)->cur_bank10 < 8u;
  }();
  static inline const bool check_regs_length = []() {
    std::shared_ptr<state10> after =
        execute_wpm10(set_prom_params10(sample10, 3u, 99u, true));
    return std::move(after)->regs10->length() == 4u;
  }();
  static inline const bool check_rom_ports_length = []() {
    std::shared_ptr<state10> after =
        execute_wpm10(set_prom_params10(sample10, 3u, 99u, true));
    return std::move(after)->rom_ports10->length() == 4u;
  }();
  static inline const bool check_sel_rom_bound = []() {
    std::shared_ptr<state10> after =
        execute_wpm10(set_prom_params10(sample10, 3u, 99u, true));
    return std::move(after)->sel_rom10 < 16u;
  }();
  static inline const bool check_stack_length = []() {
    std::shared_ptr<state10> after =
        execute_wpm10(set_prom_params10(sample10, 3u, 99u, true));
    return std::move(after)->stack10->length() <= 3u;
  }();
  static inline const bool check_prom_addr_bound = []() {
    std::shared_ptr<state10> after =
        execute_wpm10(set_prom_params10(sample10, 2048u, 99u, true));
    return std::move(after)->prom_addr10 < 4096u;
  }();
  static inline const bool check_prom_data_bound = []() {
    std::shared_ptr<state10> after =
        execute_wpm10(set_prom_params10(sample10, 3u, 155u, true));
    return std::move(after)->prom_data10 < 256u;
  }();
  static inline const bool check_rom_length = []() {
    std::shared_ptr<state10> after =
        execute_wpm10(set_prom_params10(sample10, 3u, 99u, true));
    return std::move(after)->rom10->length() == 8u;
  }();
  static inline const bool test10 =
      (((((((((check_pc_bound && check_acc_bound) && check_bank_bound) &&
             check_regs_length) &&
            check_rom_ports_length) &&
           check_sel_rom_bound) &&
          check_stack_length) &&
         check_prom_addr_bound) &&
        check_prom_data_bound) &&
       check_rom_length);

  struct state11 {
    std::shared_ptr<List<unsigned int>> rom11;
    unsigned int prom_addr11;
    unsigned int prom_data11;
    bool prom_enable11;
  };

  static std::shared_ptr<state11> execute_wpm11(std::shared_ptr<state11> s);
  static inline const std::shared_ptr<state11> sample11 =
      std::make_shared<state11>(state11{
          List<unsigned int>::cons(
              0u,
              List<unsigned int>::cons(
                  0u, List<unsigned int>::cons(0u, List<unsigned int>::nil()))),
          1u, 9u, true});
  static inline const unsigned int test11 = ListDef::template nth<unsigned int>(
      1u, execute_wpm11(sample11)->rom11, 0u);
  static inline const std::pair<
      std::pair<
          std::pair<
              std::pair<
                  std::pair<
                      std::pair<
                          std::pair<std::pair<std::pair<std::pair<unsigned int,
                                                                  unsigned int>,
                                                        unsigned int>,
                                              unsigned int>,
                                    unsigned int>,
                          bool>,
                      bool>,
                  bool>,
              bool>,
          bool>,
      unsigned int>
      t = std::make_pair(
          std::make_pair(
              std::make_pair(
                  std::make_pair(
                      std::make_pair(
                          std::make_pair(
                              std::make_pair(
                                  std::make_pair(
                                      std::make_pair(
                                          std::make_pair(test1, test2), test3),
                                      test4),
                                  test5),
                              test6),
                          test7),
                      test8),
                  test9),
              test10),
          test11);
};

template <typename T1>
T1 ListDef::nth(const unsigned int n, const std::shared_ptr<List<T1>> &l,
                const T1 default0) {
  if (n <= 0) {
    if (std::holds_alternative<typename List<T1>::Nil>(l->v())) {
      return default0;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l->v());
      return d_a0;
    }
  } else {
    unsigned int m = n - 1;
    if (std::holds_alternative<typename List<T1>::Nil>(l->v())) {
      return default0;
    } else {
      const auto &[d_a00, d_a10] = std::get<typename List<T1>::Cons>(l->v());
      return ListDef::template nth<T1>(m, d_a10, default0);
    }
  }
}

#endif // INCLUDED_PROM_OPS
