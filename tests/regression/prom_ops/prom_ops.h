#ifndef INCLUDED_PROM_OPS
#define INCLUDED_PROM_OPS

#include <any>
#include <memory>
#include <utility>
#include <variant>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  uint64_t length() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return (a1->length() + 1);
    }
  }
};

struct ListDef {
  template <typename T1>
  static T1 nth(uint64_t n, const List<T1> &l, T1 default0);
};

struct Bool {
  static bool eqb(bool b1, bool b2);
};

struct PromOps {
  static bool nat_list_eqb(const List<uint64_t> &xs, const List<uint64_t> &ys);

  template <typename T1>
  static List<T1> update_nth(uint64_t n, T1 x, const List<T1> &l) {
    if (n <= 0) {
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(x, *a1);
      }
    } else {
      uint64_t n_ = n - 1;
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[a00, a10] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(a00, update_nth<T1>(n_, x, *a10));
      }
    }
  }

  struct state1 {
    uint64_t prom_data1;
    bool prom_enable1;
  };

  static uint64_t prom_data_or_zero(const state1 &s);
  static inline const uint64_t test1 =
      prom_data_or_zero(state1{UINT64_C(77), false});

  struct state2 {
    uint64_t acc2;
    uint64_t prom_addr2;
    uint64_t prom_data2;
    bool prom_enable2;
  };

  static uint64_t flagged_sum(const state2 &s);
  static inline const uint64_t test2 =
      flagged_sum(state2{UINT64_C(3), UINT64_C(12), UINT64_C(77), false});

  struct state3 {
    uint64_t acc3;
    List<uint64_t> regs3;
    bool carry3;
    uint64_t pc3;
    List<uint64_t> stack3;
    List<uint64_t> ram_sys3;
    uint64_t cur_bank3;
    uint64_t sel_ram3;
    List<uint64_t> rom_ports3;
    uint64_t sel_rom3;
    List<uint64_t> rom3;
    bool test_pin3;
    uint64_t prom_addr3;
    uint64_t prom_data3;
    bool prom_enable3;
  };

  static state3 set_prom_params3(const state3 &s, uint64_t addr, uint64_t data,
                                 bool enable);
  static inline const uint64_t test3 = []() {
    return []() {
      state3 s =
          state3{UINT64_C(1),
                 List<uint64_t>::cons(
                     UINT64_C(2),
                     List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil())),
                 false,
                 UINT64_C(4),
                 List<uint64_t>::cons(UINT64_C(5), List<uint64_t>::nil()),
                 List<uint64_t>::cons(UINT64_C(6), List<uint64_t>::nil()),
                 UINT64_C(0),
                 UINT64_C(0),
                 List<uint64_t>::cons(UINT64_C(7), List<uint64_t>::nil()),
                 UINT64_C(0),
                 List<uint64_t>::cons(
                     UINT64_C(8),
                     List<uint64_t>::cons(UINT64_C(9), List<uint64_t>::nil())),
                 true,
                 UINT64_C(0),
                 UINT64_C(0),
                 false};
      state3 s_ =
          set_prom_params3(std::move(s), UINT64_C(21), UINT64_C(144), true);
      return ((s_.prom_addr3 +
               (s_.prom_enable3 ? std::move(s_).prom_data3 : UINT64_C(0))) +
              s_.regs3.length());
    }();
  }();
  static inline const uint64_t test4 = []() {
    return []() {
      state3 s =
          state3{UINT64_C(1),
                 List<uint64_t>::cons(
                     UINT64_C(2),
                     List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil())),
                 false,
                 UINT64_C(4),
                 List<uint64_t>::cons(UINT64_C(5), List<uint64_t>::nil()),
                 List<uint64_t>::cons(UINT64_C(6), List<uint64_t>::nil()),
                 UINT64_C(0),
                 UINT64_C(0),
                 List<uint64_t>::cons(UINT64_C(7), List<uint64_t>::nil()),
                 UINT64_C(0),
                 List<uint64_t>::cons(
                     UINT64_C(8),
                     List<uint64_t>::cons(UINT64_C(9), List<uint64_t>::nil())),
                 true,
                 UINT64_C(0),
                 UINT64_C(0),
                 false};
      state3 s_ =
          set_prom_params3(std::move(s), UINT64_C(21), UINT64_C(144), true);
      return ((s_.prom_addr3 +
               (s_.prom_enable3 ? std::move(s_).prom_data3 : UINT64_C(0))) +
              s_.regs3.length());
    }();
  }();

  struct state5 {
    uint64_t acc5;
    List<uint64_t> regs5;
    List<uint64_t> rom5;
    uint64_t prom_addr5;
    uint64_t prom_data5;
    bool prom_enable5;
  };

  static state5 set_prom_params5(const state5 &s, uint64_t addr, uint64_t data,
                                 bool enable);
  static inline const uint64_t test5 = []() {
    return []() {
      state5 s = state5{
          UINT64_C(3),
          List<uint64_t>::cons(
              UINT64_C(1),
              List<uint64_t>::cons(UINT64_C(2), List<uint64_t>::nil())),
          List<uint64_t>::cons(
              UINT64_C(9),
              List<uint64_t>::cons(
                  UINT64_C(8),
                  List<uint64_t>::cons(UINT64_C(7), List<uint64_t>::nil()))),
          UINT64_C(0),
          UINT64_C(0),
          false};
      state5 s_ =
          set_prom_params5(std::move(s), UINT64_C(23), UINT64_C(77), true);
      return ((s_.acc5 + s_.prom_addr5) +
              (s_.prom_enable5 ? std::move(s_).prom_data5 : UINT64_C(0)));
    }();
  }();

  struct state6 {
    List<uint64_t> rom6;
    uint64_t prom_addr6;
    uint64_t prom_data6;
    bool prom_enable6;
  };

  static state6 set_prom_params6(const state6 &s, uint64_t addr, uint64_t data,
                                 bool enable);
  static inline const state6 sample6 = state6{
      List<uint64_t>::cons(
          UINT64_C(10),
          List<uint64_t>::cons(
              UINT64_C(11),
              List<uint64_t>::cons(
                  UINT64_C(12),
                  List<uint64_t>::cons(UINT64_C(13), List<uint64_t>::nil())))),
      UINT64_C(0), UINT64_C(0), false};
  static inline const bool test6 = Bool::eqb(
      set_prom_params6(sample6, UINT64_C(2), UINT64_C(99), true).prom_enable6,
      true);

  struct state7 {
    List<uint64_t> regs7;
    List<uint64_t> ram_sys7;
    uint64_t prom_addr7;
    uint64_t prom_data7;
    bool prom_enable7;
  };

  static state7 set_prom_params7(const state7 &s, uint64_t addr, uint64_t data,
                                 bool enable);
  static inline const state7 sample7 =
      state7{List<uint64_t>::cons(
                 UINT64_C(1),
                 List<uint64_t>::cons(
                     UINT64_C(2),
                     List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()))),
             List<uint64_t>::cons(
                 UINT64_C(9),
                 List<uint64_t>::cons(
                     UINT64_C(8),
                     List<uint64_t>::cons(UINT64_C(7), List<uint64_t>::nil()))),
             UINT64_C(0), UINT64_C(0), false};
  static inline const bool test7 = nat_list_eqb(
      set_prom_params7(sample7, UINT64_C(12), UINT64_C(99), true).ram_sys7,
      sample7.ram_sys7);

  struct state8 {
    List<uint64_t> regs8;
    List<uint64_t> ram_sys8;
    uint64_t prom_addr8;
    uint64_t prom_data8;
    bool prom_enable8;
  };

  static state8 set_prom_params8(const state8 &s, uint64_t addr, uint64_t data,
                                 bool enable);
  static inline const state8 sample8 =
      state8{List<uint64_t>::cons(
                 UINT64_C(1),
                 List<uint64_t>::cons(
                     UINT64_C(2),
                     List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()))),
             List<uint64_t>::cons(
                 UINT64_C(9),
                 List<uint64_t>::cons(UINT64_C(8), List<uint64_t>::nil())),
             UINT64_C(0), UINT64_C(0), false};
  static inline const bool test8 = nat_list_eqb(
      set_prom_params8(sample8, UINT64_C(12), UINT64_C(99), true).regs8,
      sample8.regs8);

  struct state9 {
    List<uint64_t> rom9;
    uint64_t prom_addr9;
    uint64_t prom_data9;
    bool prom_enable9;
  };

  static state9 set_prom_params9(const state9 &s, uint64_t addr, uint64_t data,
                                 bool enable);
  static inline const state9 sample9 = state9{
      List<uint64_t>::cons(
          UINT64_C(10),
          List<uint64_t>::cons(
              UINT64_C(11),
              List<uint64_t>::cons(
                  UINT64_C(12),
                  List<uint64_t>::cons(UINT64_C(13), List<uint64_t>::nil())))),
      UINT64_C(0), UINT64_C(0), false};
  static inline const bool test9 =
      set_prom_params9(sample9, UINT64_C(12), UINT64_C(99), true)
          .rom9.length() == sample9.rom9.length();

  struct state10 {
    List<uint64_t> regs10;
    List<uint64_t> rom10;
    uint64_t acc10;
    uint64_t pc10;
    List<uint64_t> stack10;
    uint64_t cur_bank10;
    List<uint64_t> rom_ports10;
    uint64_t sel_rom10;
    uint64_t prom_addr10;
    uint64_t prom_data10;
    bool prom_enable10;
  };

  static state10 set_prom_params10(const state10 &s, uint64_t addr,
                                   uint64_t data, bool enable);
  static state10 execute_wpm10(const state10 &s);
  static inline const state10 sample10 = state10{
      List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(
              UINT64_C(2),
              List<uint64_t>::cons(
                  UINT64_C(3),
                  List<uint64_t>::cons(UINT64_C(4), List<uint64_t>::nil())))),
      List<uint64_t>::cons(
          UINT64_C(10),
          List<uint64_t>::cons(
              UINT64_C(11),
              List<uint64_t>::cons(
                  UINT64_C(12),
                  List<uint64_t>::cons(
                      UINT64_C(13),
                      List<uint64_t>::cons(
                          UINT64_C(14),
                          List<uint64_t>::cons(
                              UINT64_C(15),
                              List<uint64_t>::cons(
                                  UINT64_C(16),
                                  List<uint64_t>::cons(
                                      UINT64_C(17),
                                      List<uint64_t>::nil())))))))),
      UINT64_C(7),
      UINT64_C(1025),
      List<uint64_t>::cons(
          UINT64_C(7),
          List<uint64_t>::cons(UINT64_C(9), List<uint64_t>::nil())),
      UINT64_C(2),
      List<uint64_t>::cons(
          UINT64_C(3),
          List<uint64_t>::cons(
              UINT64_C(4),
              List<uint64_t>::cons(
                  UINT64_C(5),
                  List<uint64_t>::cons(UINT64_C(6), List<uint64_t>::nil())))),
      UINT64_C(5),
      UINT64_C(0),
      UINT64_C(0),
      false};
  static inline const bool check_pc_bound = []() {
    state10 after = execute_wpm10(
        set_prom_params10(sample10, UINT64_C(3), UINT64_C(99), true));
    return std::move(after).pc10 < UINT64_C(4096);
  }();
  static inline const bool check_acc_bound = []() {
    state10 after = execute_wpm10(
        set_prom_params10(sample10, UINT64_C(3), UINT64_C(99), true));
    return std::move(after).acc10 < UINT64_C(16);
  }();
  static inline const bool check_bank_bound = []() {
    state10 after = execute_wpm10(
        set_prom_params10(sample10, UINT64_C(3), UINT64_C(99), true));
    return std::move(after).cur_bank10 < UINT64_C(8);
  }();
  static inline const bool check_regs_length = []() {
    state10 after = execute_wpm10(
        set_prom_params10(sample10, UINT64_C(3), UINT64_C(99), true));
    return std::move(after).regs10.length() == UINT64_C(4);
  }();
  static inline const bool check_rom_ports_length = []() {
    state10 after = execute_wpm10(
        set_prom_params10(sample10, UINT64_C(3), UINT64_C(99), true));
    return std::move(after).rom_ports10.length() == UINT64_C(4);
  }();
  static inline const bool check_sel_rom_bound = []() {
    state10 after = execute_wpm10(
        set_prom_params10(sample10, UINT64_C(3), UINT64_C(99), true));
    return std::move(after).sel_rom10 < UINT64_C(16);
  }();
  static inline const bool check_stack_length = []() {
    state10 after = execute_wpm10(
        set_prom_params10(sample10, UINT64_C(3), UINT64_C(99), true));
    return std::move(after).stack10.length() <= UINT64_C(3);
  }();
  static inline const bool check_prom_addr_bound = []() {
    state10 after = execute_wpm10(
        set_prom_params10(sample10, UINT64_C(2048), UINT64_C(99), true));
    return std::move(after).prom_addr10 < UINT64_C(4096);
  }();
  static inline const bool check_prom_data_bound = []() {
    state10 after = execute_wpm10(
        set_prom_params10(sample10, UINT64_C(3), UINT64_C(155), true));
    return std::move(after).prom_data10 < UINT64_C(256);
  }();
  static inline const bool check_rom_length = []() {
    state10 after = execute_wpm10(
        set_prom_params10(sample10, UINT64_C(3), UINT64_C(99), true));
    return std::move(after).rom10.length() == UINT64_C(8);
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
    List<uint64_t> rom11;
    uint64_t prom_addr11;
    uint64_t prom_data11;
    bool prom_enable11;
  };

  static state11 execute_wpm11(state11 s);
  static inline const state11 sample11 = state11{
      List<uint64_t>::cons(
          UINT64_C(0),
          List<uint64_t>::cons(
              UINT64_C(0),
              List<uint64_t>::cons(UINT64_C(0), List<uint64_t>::nil()))),
      UINT64_C(1), UINT64_C(9), true};
  static inline const uint64_t test11 = ListDef::template nth<uint64_t>(
      UINT64_C(1), execute_wpm11(sample11).rom11, UINT64_C(0));
  static inline const std::pair<
      std::pair<
          std::pair<
              std::pair<
                  std::pair<
                      std::pair<
                          std::pair<
                              std::pair<std::pair<std::pair<uint64_t, uint64_t>,
                                                  uint64_t>,
                                        uint64_t>,
                              uint64_t>,
                          bool>,
                      bool>,
                  bool>,
              bool>,
          bool>,
      uint64_t>
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
T1 ListDef::nth(uint64_t n, const List<T1> &l, T1 default0) {
  if (n <= 0) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      return a0;
    }
  } else {
    uint64_t m = n - 1;
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a00, a10] = std::get<typename List<T1>::Cons>(l.v());
      return ListDef::template nth<T1>(m, *a10, default0);
    }
  }
}

#endif // INCLUDED_PROM_OPS
