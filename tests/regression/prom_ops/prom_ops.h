#ifndef INCLUDED_PROM_OPS
#define INCLUDED_PROM_OPS

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A> struct List;

struct Bool {
  static bool eqb(bool b1, bool b2);
};

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

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_(crane_convert_spine(
            _other, std::shared_ptr<List<A>>(nullptr),
            [](const List<CraneU> &_cell) -> const List<CraneU> * {
              if (std::holds_alternative<typename List<CraneU>::Cons>(
                      _cell.v())) {
                return std::get<typename List<CraneU>::Cons>(_cell.v()).l.get();
              } else {
                return nullptr;
              }
            },
            [&](const List<CraneU> &_other,
                std::shared_ptr<List<A>> _below) -> variant_t {
              if (std::holds_alternative<typename List<CraneU>::Nil>(
                      _other.v())) {
                return Nil{};
              } else {
                const auto &[a, l] =
                    std::get<typename List<CraneU>::Cons>(_other.v());
                return Cons{
                    [&]() -> A {
                      if constexpr (crane_convertible<A, const CraneU &>) {
                        return crane_convert<A>(a);
                      } else {
                        throw std::logic_error(
                            "unreachable: inactive constructor field at this "
                            "instantiation");
                      }
                    }(),
                    std::move(_below)};
              }
            },
            [](auto &&_alt) {
              return std::make_shared<List<A>>(std::move(_alt));
            })) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) = default;
  List &operator=(List &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  uint64_t length() const {
    const List<A> *_self = this;

    /// CraneEnter: captures varying parameters for each recursive call.
    struct CraneEnter {
      const List<A> *_self;
    };

    /// CraneCont_Cons: resumes after recursive call, then processes rest.
    struct CraneCont_Cons {};

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    uint64_t _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{_self});
    /// Loopified length: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(CraneCont_Cons{});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }
};

struct ListDef {
  template <typename T1>
  static T1 nth(uint64_t n, const List<T1> &l, T1 default0);
};

struct PromOps {
  static bool nat_list_eqb(const List<uint64_t> &xs, const List<uint64_t> &ys);

  template <typename T1>
  static List<T1> update_nth(uint64_t n, const T1 &x, const List<T1> &l) {
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
  static constexpr uint64_t test1 = UINT64_C(0);

  struct state2 {
    uint64_t acc2;
    uint64_t prom_addr2;
    uint64_t prom_data2;
    bool prom_enable2;
  };

  static uint64_t flagged_sum(const state2 &s);
  static constexpr uint64_t test2 = UINT64_C(15);

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
  static constexpr uint64_t test3 = UINT64_C(167);
  static constexpr uint64_t test4 = UINT64_C(167);

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
  static constexpr uint64_t test5 = UINT64_C(103);

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
  static constexpr bool test6 = true;

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
  static constexpr bool test9 = true;

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
  static constexpr bool check_pc_bound = true;
  static constexpr bool check_acc_bound = true;
  static constexpr bool check_bank_bound = true;
  static constexpr bool check_regs_length = true;
  static constexpr bool check_rom_ports_length = true;
  static constexpr bool check_sel_rom_bound = true;
  static constexpr bool check_stack_length = true;
  static constexpr bool check_prom_addr_bound = true;
  static constexpr bool check_prom_data_bound = true;
  static constexpr bool check_rom_length = true;
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
  static constexpr uint64_t test11 = UINT64_C(9);
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
      return ListDef::template nth<T1>(m, *a10, std::move(default0));
    }
  }
}

#endif // INCLUDED_PROM_OPS
