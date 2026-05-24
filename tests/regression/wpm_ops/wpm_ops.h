#ifndef INCLUDED_WPM_OPS
#define INCLUDED_WPM_OPS

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
};

struct ListDef {
  template <typename T1>
  static T1 nth(uint64_t n, const List<T1> &l, T1 default0);
};

struct WpmOps {
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

  static bool nat_list_eqb(const List<uint64_t> &xs, const List<uint64_t> &ys);

  struct state1 {
    List<uint64_t> rom1;
    uint64_t prom_addr1;
    uint64_t prom_data1;
    bool prom_enable1;

    // ACCESSORS
    state1 clone() const {
      return state1{this->rom1, this->prom_addr1, this->prom_data1,
                    this->prom_enable1};
    }
  };

  static state1 execute_wpm1(const state1 &s);
  static inline const state1 sample1 = state1{
      List<uint64_t>::cons(
          UINT64_C(10),
          List<uint64_t>::cons(
              UINT64_C(11),
              List<uint64_t>::cons(
                  UINT64_C(12),
                  List<uint64_t>::cons(UINT64_C(13), List<uint64_t>::nil())))),
      UINT64_C(2), UINT64_C(99), false};
  static inline const state1 after1 = execute_wpm1(sample1);
  static inline const bool test_wpm_disabled_is_nop =
      (ListDef::template nth<uint64_t>(UINT64_C(0), after1.rom1, UINT64_C(0)) ==
           UINT64_C(10) &&
       (ListDef::template nth<uint64_t>(UINT64_C(1), after1.rom1,
                                        UINT64_C(0)) == UINT64_C(11) &&
        (ListDef::template nth<uint64_t>(UINT64_C(2), after1.rom1,
                                         UINT64_C(0)) == UINT64_C(12) &&
         ListDef::template nth<uint64_t>(UINT64_C(3), after1.rom1,
                                         UINT64_C(0)) == UINT64_C(13))));

  struct state2 {
    List<uint64_t> ram_sys2;
    List<uint64_t> rom2;
    uint64_t prom_addr2;
    uint64_t prom_data2;
    bool prom_enable2;

    // ACCESSORS
    state2 clone() const {
      return state2{this->ram_sys2, this->rom2, this->prom_addr2,
                    this->prom_data2, this->prom_enable2};
    }
  };

  static state2 execute_wpm2(const state2 &s);
  static inline const state2 sample2 = state2{
      List<uint64_t>::cons(
          UINT64_C(5),
          List<uint64_t>::cons(
              UINT64_C(6),
              List<uint64_t>::cons(UINT64_C(7), List<uint64_t>::nil()))),
      List<uint64_t>::cons(
          UINT64_C(10),
          List<uint64_t>::cons(
              UINT64_C(11),
              List<uint64_t>::cons(UINT64_C(12), List<uint64_t>::nil()))),
      UINT64_C(1), UINT64_C(99), true};
  static inline const bool test_wpm_enabled_preserves_ram =
      nat_list_eqb(execute_wpm2(sample2).ram_sys2, sample2.ram_sys2);

  struct state3 {
    List<uint64_t> regs3;
    List<uint64_t> rom3;
    uint64_t prom_addr3;
    uint64_t prom_data3;
    bool prom_enable3;

    // ACCESSORS
    state3 clone() const {
      return state3{this->regs3, this->rom3, this->prom_addr3, this->prom_data3,
                    this->prom_enable3};
    }
  };

  static state3 execute_wpm3(const state3 &s);
  static inline const state3 sample3 = state3{
      List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(
              UINT64_C(2),
              List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()))),
      List<uint64_t>::cons(
          UINT64_C(10),
          List<uint64_t>::cons(
              UINT64_C(11),
              List<uint64_t>::cons(UINT64_C(12), List<uint64_t>::nil()))),
      UINT64_C(1), UINT64_C(99), true};
  static inline const bool test_wpm_enabled_preserves_regs =
      nat_list_eqb(execute_wpm3(sample3).regs3, sample3.regs3);

  struct state4 {
    List<uint64_t> rom4;
    uint64_t prom_addr4;
    uint64_t prom_data4;
    bool prom_enable4;

    // ACCESSORS
    state4 clone() const {
      return state4{this->rom4, this->prom_addr4, this->prom_data4,
                    this->prom_enable4};
    }
  };

  static state4 execute_wpm4(const state4 &s);
  static inline const uint64_t test_wpm_update_gate = []() {
    state4 s = state4{
        List<uint64_t>::cons(
            UINT64_C(10),
            List<uint64_t>::cons(
                UINT64_C(11),
                List<uint64_t>::cons(UINT64_C(12), List<uint64_t>::nil()))),
        UINT64_C(1), UINT64_C(99), true};
    state4 s_ = execute_wpm4(std::move(s));
    return ListDef::template nth<uint64_t>(UINT64_C(1), std::move(s_).rom4,
                                           UINT64_C(0));
  }();

  struct state5 {
    List<uint64_t> rom5;
    uint64_t prom_addr5;
    uint64_t prom_data5;
    bool prom_enable5;

    // ACCESSORS
    state5 clone() const {
      return state5{this->rom5, this->prom_addr5, this->prom_data5,
                    this->prom_enable5};
    }
  };

  static state5 execute_wpm5(const state5 &s);
  static inline const state5 sample5 = state5{
      List<uint64_t>::cons(
          UINT64_C(10),
          List<uint64_t>::cons(
              UINT64_C(11),
              List<uint64_t>::cons(
                  UINT64_C(12),
                  List<uint64_t>::cons(UINT64_C(13), List<uint64_t>::nil())))),
      UINT64_C(2), UINT64_C(99), true};
  static inline const bool test_wpm_updates_rom_at_addr =
      ListDef::template nth<uint64_t>(UINT64_C(2), execute_wpm5(sample5).rom5,
                                      UINT64_C(0)) == UINT64_C(99);

  struct state6 {
    List<uint64_t> rom6;
    uint64_t prom_addr6;
    uint64_t prom_data6;
    bool prom_enable6;

    // ACCESSORS
    state6 clone() const {
      return state6{this->rom6, this->prom_addr6, this->prom_data6,
                    this->prom_enable6};
    }
  };

  static state6 execute_wpm6(const state6 &s);
  static inline const state6 sample6 = state6{
      List<uint64_t>::cons(
          UINT64_C(10),
          List<uint64_t>::cons(
              UINT64_C(11),
              List<uint64_t>::cons(
                  UINT64_C(12),
                  List<uint64_t>::cons(UINT64_C(13), List<uint64_t>::nil())))),
      UINT64_C(2), UINT64_C(99), true};
  static inline const state6 after6 = execute_wpm6(sample6);
  static inline const bool test_wpm_writes_exactly_once =
      (ListDef::template nth<uint64_t>(UINT64_C(2), after6.rom6, UINT64_C(0)) ==
           UINT64_C(99) &&
       (ListDef::template nth<uint64_t>(UINT64_C(0), after6.rom6,
                                        UINT64_C(0)) == UINT64_C(10) &&
        (ListDef::template nth<uint64_t>(UINT64_C(1), after6.rom6,
                                         UINT64_C(0)) == UINT64_C(11) &&
         ListDef::template nth<uint64_t>(UINT64_C(3), after6.rom6,
                                         UINT64_C(0)) == UINT64_C(13))));
  static inline const std::pair<
      std::pair<std::pair<std::pair<std::pair<bool, bool>, bool>, uint64_t>,
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

#endif // INCLUDED_WPM_OPS
