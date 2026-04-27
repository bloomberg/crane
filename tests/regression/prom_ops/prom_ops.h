#ifndef INCLUDED_PROM_OPS
#define INCLUDED_PROM_OPS

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;
  using crane_element_type = t_A;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  __attribute__((pure)) List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      t_A __c0;
      if constexpr (
          requires { d_a0 ? 0 : 0; } && requires { *d_a0; } &&
          requires { d_a0->clone(); } && requires { d_a0.get(); }) {
        using _E = std::remove_cvref_t<decltype(*d_a0)>;
        __c0 = d_a0 ? std::make_unique<_E>(d_a0->clone()) : nullptr;
      } else if constexpr (requires { d_a0.clone(); }) {
        __c0 = d_a0.clone();
      } else {
        __c0 = d_a0;
      }
      return List<t_A>(
          Cons{std::move(__c0),
               d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ = Cons{
          [&]<typename _DstT = t_A>(auto &&__v) -> _DstT {
            if constexpr (
                requires { *__v; } &&
                !requires { std::declval<_DstT>().get(); })
              return _DstT(*__v);
            else if constexpr (
                !requires { *__v; } &&
                requires { std::declval<_DstT>().get(); }) {
              using _E =
                  std::remove_pointer_t<decltype(std::declval<_DstT>().get())>;
              return std::make_unique<_E>(std::move(__v));
            } else
              return _DstT(__v);
          }(d_a0),
          d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) List<t_A> *operator->() { return this; }

  __attribute__((pure)) const List<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = List<t_A>(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) unsigned int length() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return ((*(d_a1)).length() + 1);
    }
  }
};

struct ListDef {
  template <typename T1>
  static T1 nth(const unsigned int &n, const List<T1> &l, const T1 default0);
};

struct Bool {
  __attribute__((pure)) static bool eqb(const bool &b1, const bool &b2);
};

struct PromOps {
  __attribute__((pure)) static bool nat_list_eqb(const List<unsigned int> &xs,
                                                 const List<unsigned int> &ys);

  template <typename T1>
  __attribute__((pure)) static List<T1>
  update_nth(const unsigned int &n, const T1 x, const List<T1> &l) {
    if (n <= 0) {
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(x, *(d_a1));
      }
    } else {
      unsigned int n_ = n - 1;
      if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[d_a00, d_a10] = std::get<typename List<T1>::Cons>(l.v());
        return List<T1>::cons(d_a00, update_nth<T1>(n_, x, *(d_a10)));
      }
    }
  }

  struct state1 {
    unsigned int prom_data1;
    bool prom_enable1;

    __attribute__((pure)) state1 *operator->() { return this; }

    __attribute__((pure)) const state1 *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) state1 clone() const {
      return state1{
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).prom_data1),
          [](auto &&__v) -> bool {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).prom_enable1)};
    }
  };

  __attribute__((pure)) static unsigned int prom_data_or_zero(const state1 &s);
  static inline const unsigned int test1 =
      prom_data_or_zero(state1{77u, false});

  struct state2 {
    unsigned int acc2;
    unsigned int prom_addr2;
    unsigned int prom_data2;
    bool prom_enable2;

    __attribute__((pure)) state2 *operator->() { return this; }

    __attribute__((pure)) const state2 *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) state2 clone() const {
      return state2{
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).acc2),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).prom_addr2),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).prom_data2),
          [](auto &&__v) -> bool {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).prom_enable2)};
    }
  };

  __attribute__((pure)) static unsigned int flagged_sum(const state2 &s);
  static inline const unsigned int test2 =
      flagged_sum(state2{3u, 12u, 77u, false});

  struct state3 {
    unsigned int acc3;
    List<unsigned int> regs3;
    bool carry3;
    unsigned int pc3;
    List<unsigned int> stack3;
    List<unsigned int> ram_sys3;
    unsigned int cur_bank3;
    unsigned int sel_ram3;
    List<unsigned int> rom_ports3;
    unsigned int sel_rom3;
    List<unsigned int> rom3;
    bool test_pin3;
    unsigned int prom_addr3;
    unsigned int prom_data3;
    bool prom_enable3;

    __attribute__((pure)) state3 *operator->() { return this; }

    __attribute__((pure)) const state3 *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) state3 clone() const {
      return state3{
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).acc3),
          (*(this)).regs3.clone(),
          [](auto &&__v) -> bool {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).carry3),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).pc3),
          (*(this)).stack3.clone(),
          (*(this)).ram_sys3.clone(),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).cur_bank3),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).sel_ram3),
          (*(this)).rom_ports3.clone(),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).sel_rom3),
          (*(this)).rom3.clone(),
          [](auto &&__v) -> bool {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).test_pin3),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).prom_addr3),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).prom_data3),
          [](auto &&__v) -> bool {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).prom_enable3)};
    }
  };

  __attribute__((pure)) static state3 set_prom_params3(const state3 &s,
                                                       unsigned int addr,
                                                       unsigned int data,
                                                       bool enable);
  static inline const unsigned int test3 = []() {
    return []() {
      state3 s = state3{
          1u,
          List<unsigned int>::cons(
              2u, List<unsigned int>::cons(3u, List<unsigned int>::nil())),
          false,
          4u,
          List<unsigned int>::cons(5u, List<unsigned int>::nil()),
          List<unsigned int>::cons(6u, List<unsigned int>::nil()),
          0u,
          0u,
          List<unsigned int>::cons(7u, List<unsigned int>::nil()),
          0u,
          List<unsigned int>::cons(
              8u, List<unsigned int>::cons(9u, List<unsigned int>::nil())),
          true,
          0u,
          0u,
          false};
      state3 s_ = set_prom_params3(s, 21u, 144u, true);
      return ((s_.prom_addr3 + [&]() -> unsigned int {
                if (s_.prom_enable3) {
                  return s_.prom_data3;
                } else {
                  return 0u;
                }
              }()) +
              s_.regs3.length());
    }();
  }();
  static inline const unsigned int test4 = []() {
    return []() {
      state3 s = state3{
          1u,
          List<unsigned int>::cons(
              2u, List<unsigned int>::cons(3u, List<unsigned int>::nil())),
          false,
          4u,
          List<unsigned int>::cons(5u, List<unsigned int>::nil()),
          List<unsigned int>::cons(6u, List<unsigned int>::nil()),
          0u,
          0u,
          List<unsigned int>::cons(7u, List<unsigned int>::nil()),
          0u,
          List<unsigned int>::cons(
              8u, List<unsigned int>::cons(9u, List<unsigned int>::nil())),
          true,
          0u,
          0u,
          false};
      state3 s_ = set_prom_params3(s, 21u, 144u, true);
      return ((s_.prom_addr3 + [&]() -> unsigned int {
                if (s_.prom_enable3) {
                  return s_.prom_data3;
                } else {
                  return 0u;
                }
              }()) +
              s_.regs3.length());
    }();
  }();

  struct state5 {
    unsigned int acc5;
    List<unsigned int> regs5;
    List<unsigned int> rom5;
    unsigned int prom_addr5;
    unsigned int prom_data5;
    bool prom_enable5;

    __attribute__((pure)) state5 *operator->() { return this; }

    __attribute__((pure)) const state5 *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) state5 clone() const {
      return state5{
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).acc5),
          (*(this)).regs5.clone(),
          (*(this)).rom5.clone(),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).prom_addr5),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).prom_data5),
          [](auto &&__v) -> bool {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).prom_enable5)};
    }
  };

  __attribute__((pure)) static state5 set_prom_params5(const state5 &s,
                                                       unsigned int addr,
                                                       unsigned int data,
                                                       bool enable);
  static inline const unsigned int test5 = []() {
    return []() {
      state5 s = state5{
          3u,
          List<unsigned int>::cons(
              1u, List<unsigned int>::cons(2u, List<unsigned int>::nil())),
          List<unsigned int>::cons(
              9u,
              List<unsigned int>::cons(
                  8u, List<unsigned int>::cons(7u, List<unsigned int>::nil()))),
          0u,
          0u,
          false};
      state5 s_ = set_prom_params5(s, 23u, 77u, true);
      return ((s_.acc5 + s_.prom_addr5) + [&]() -> unsigned int {
        if (s_.prom_enable5) {
          return s_.prom_data5;
        } else {
          return 0u;
        }
      }());
    }();
  }();

  struct state6 {
    List<unsigned int> rom6;
    unsigned int prom_addr6;
    unsigned int prom_data6;
    bool prom_enable6;

    __attribute__((pure)) state6 *operator->() { return this; }

    __attribute__((pure)) const state6 *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) state6 clone() const {
      return state6{
          (*(this)).rom6.clone(),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).prom_addr6),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).prom_data6),
          [](auto &&__v) -> bool {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).prom_enable6)};
    }
  };

  __attribute__((pure)) static state6 set_prom_params6(const state6 &s,
                                                       unsigned int addr,
                                                       unsigned int data,
                                                       bool enable);
  static inline const state6 sample6 =
      state6{List<unsigned int>::cons(
                 10u, List<unsigned int>::cons(
                          11u, List<unsigned int>::cons(
                                   12u, List<unsigned int>::cons(
                                            13u, List<unsigned int>::nil())))),
             0u, 0u, false};
  static inline const bool test6 =
      Bool::eqb(set_prom_params6(sample6, 2u, 99u, true).prom_enable6, true);

  struct state7 {
    List<unsigned int> regs7;
    List<unsigned int> ram_sys7;
    unsigned int prom_addr7;
    unsigned int prom_data7;
    bool prom_enable7;

    __attribute__((pure)) state7 *operator->() { return this; }

    __attribute__((pure)) const state7 *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) state7 clone() const {
      return state7{
          (*(this)).regs7.clone(), (*(this)).ram_sys7.clone(),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).prom_addr7),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).prom_data7),
          [](auto &&__v) -> bool {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).prom_enable7)};
    }
  };

  __attribute__((pure)) static state7 set_prom_params7(const state7 &s,
                                                       unsigned int addr,
                                                       unsigned int data,
                                                       bool enable);
  static inline const state7 sample7 = state7{
      List<unsigned int>::cons(
          1u, List<unsigned int>::cons(
                  2u, List<unsigned int>::cons(3u, List<unsigned int>::nil()))),
      List<unsigned int>::cons(
          9u, List<unsigned int>::cons(
                  8u, List<unsigned int>::cons(7u, List<unsigned int>::nil()))),
      0u, 0u, false};
  static inline const bool test7 = nat_list_eqb(
      set_prom_params7(sample7, 12u, 99u, true).ram_sys7, sample7.ram_sys7);

  struct state8 {
    List<unsigned int> regs8;
    List<unsigned int> ram_sys8;
    unsigned int prom_addr8;
    unsigned int prom_data8;
    bool prom_enable8;

    __attribute__((pure)) state8 *operator->() { return this; }

    __attribute__((pure)) const state8 *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) state8 clone() const {
      return state8{
          (*(this)).regs8.clone(), (*(this)).ram_sys8.clone(),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).prom_addr8),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).prom_data8),
          [](auto &&__v) -> bool {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).prom_enable8)};
    }
  };

  __attribute__((pure)) static state8 set_prom_params8(const state8 &s,
                                                       unsigned int addr,
                                                       unsigned int data,
                                                       bool enable);
  static inline const state8 sample8 = state8{
      List<unsigned int>::cons(
          1u, List<unsigned int>::cons(
                  2u, List<unsigned int>::cons(3u, List<unsigned int>::nil()))),
      List<unsigned int>::cons(
          9u, List<unsigned int>::cons(8u, List<unsigned int>::nil())),
      0u, 0u, false};
  static inline const bool test8 = nat_list_eqb(
      set_prom_params8(sample8, 12u, 99u, true).regs8, sample8.regs8);

  struct state9 {
    List<unsigned int> rom9;
    unsigned int prom_addr9;
    unsigned int prom_data9;
    bool prom_enable9;

    __attribute__((pure)) state9 *operator->() { return this; }

    __attribute__((pure)) const state9 *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) state9 clone() const {
      return state9{
          (*(this)).rom9.clone(),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).prom_addr9),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).prom_data9),
          [](auto &&__v) -> bool {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).prom_enable9)};
    }
  };

  __attribute__((pure)) static state9 set_prom_params9(const state9 &s,
                                                       unsigned int addr,
                                                       unsigned int data,
                                                       bool enable);
  static inline const state9 sample9 =
      state9{List<unsigned int>::cons(
                 10u, List<unsigned int>::cons(
                          11u, List<unsigned int>::cons(
                                   12u, List<unsigned int>::cons(
                                            13u, List<unsigned int>::nil())))),
             0u, 0u, false};
  static inline const bool test9 =
      set_prom_params9(sample9, 12u, 99u, true).rom9.length() ==
      sample9.rom9.length();

  struct state10 {
    List<unsigned int> regs10;
    List<unsigned int> rom10;
    unsigned int acc10;
    unsigned int pc10;
    List<unsigned int> stack10;
    unsigned int cur_bank10;
    List<unsigned int> rom_ports10;
    unsigned int sel_rom10;
    unsigned int prom_addr10;
    unsigned int prom_data10;
    bool prom_enable10;

    __attribute__((pure)) state10 *operator->() { return this; }

    __attribute__((pure)) const state10 *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) state10 clone() const {
      return state10{
          (*(this)).regs10.clone(),
          (*(this)).rom10.clone(),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).acc10),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).pc10),
          (*(this)).stack10.clone(),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).cur_bank10),
          (*(this)).rom_ports10.clone(),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).sel_rom10),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).prom_addr10),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).prom_data10),
          [](auto &&__v) -> bool {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).prom_enable10)};
    }
  };

  __attribute__((pure)) static state10 set_prom_params10(const state10 &s,
                                                         unsigned int addr,
                                                         unsigned int data,
                                                         bool enable);
  __attribute__((pure)) static state10 execute_wpm10(const state10 &s);
  static inline const state10 sample10 = state10{
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
                                      17u, List<unsigned int>::nil())))))))),
      7u,
      1025u,
      List<unsigned int>::cons(
          7u, List<unsigned int>::cons(9u, List<unsigned int>::nil())),
      2u,
      List<unsigned int>::cons(
          3u, List<unsigned int>::cons(
                  4u, List<unsigned int>::cons(
                          5u, List<unsigned int>::cons(
                                  6u, List<unsigned int>::nil())))),
      5u,
      0u,
      0u,
      false};
  static inline const bool check_pc_bound = []() {
    state10 after = execute_wpm10(set_prom_params10(sample10, 3u, 99u, true));
    return after.pc10 < 4096u;
  }();
  static inline const bool check_acc_bound = []() {
    state10 after = execute_wpm10(set_prom_params10(sample10, 3u, 99u, true));
    return after.acc10 < 16u;
  }();
  static inline const bool check_bank_bound = []() {
    state10 after = execute_wpm10(set_prom_params10(sample10, 3u, 99u, true));
    return after.cur_bank10 < 8u;
  }();
  static inline const bool check_regs_length = []() {
    state10 after = execute_wpm10(set_prom_params10(sample10, 3u, 99u, true));
    return after.regs10.length() == 4u;
  }();
  static inline const bool check_rom_ports_length = []() {
    state10 after = execute_wpm10(set_prom_params10(sample10, 3u, 99u, true));
    return after.rom_ports10.length() == 4u;
  }();
  static inline const bool check_sel_rom_bound = []() {
    state10 after = execute_wpm10(set_prom_params10(sample10, 3u, 99u, true));
    return after.sel_rom10 < 16u;
  }();
  static inline const bool check_stack_length = []() {
    state10 after = execute_wpm10(set_prom_params10(sample10, 3u, 99u, true));
    return after.stack10.length() <= 3u;
  }();
  static inline const bool check_prom_addr_bound = []() {
    state10 after =
        execute_wpm10(set_prom_params10(sample10, 2048u, 99u, true));
    return after.prom_addr10 < 4096u;
  }();
  static inline const bool check_prom_data_bound = []() {
    state10 after = execute_wpm10(set_prom_params10(sample10, 3u, 155u, true));
    return after.prom_data10 < 256u;
  }();
  static inline const bool check_rom_length = []() {
    state10 after = execute_wpm10(set_prom_params10(sample10, 3u, 99u, true));
    return after.rom10.length() == 8u;
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
    List<unsigned int> rom11;
    unsigned int prom_addr11;
    unsigned int prom_data11;
    bool prom_enable11;

    __attribute__((pure)) state11 *operator->() { return this; }

    __attribute__((pure)) const state11 *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) state11 clone() const {
      return state11{
          (*(this)).rom11.clone(),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).prom_addr11),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).prom_data11),
          [](auto &&__v) -> bool {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).prom_enable11)};
    }
  };

  __attribute__((pure)) static state11 execute_wpm11(state11 s);
  static inline const state11 sample11 = state11{
      List<unsigned int>::cons(
          0u, List<unsigned int>::cons(
                  0u, List<unsigned int>::cons(0u, List<unsigned int>::nil()))),
      1u, 9u, true};
  static inline const unsigned int test11 = ListDef::template nth<unsigned int>(
      1u, execute_wpm11(sample11).rom11, 0u);
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
T1 ListDef::nth(const unsigned int &n, const List<T1> &l, const T1 default0) {
  if (n <= 0) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
      return d_a0;
    }
  } else {
    unsigned int m = n - 1;
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[d_a00, d_a10] = std::get<typename List<T1>::Cons>(l.v());
      return ListDef::template nth<T1>(m, *(d_a10), default0);
    }
  }
}

#endif // INCLUDED_PROM_OPS
