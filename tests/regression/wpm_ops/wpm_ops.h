#ifndef INCLUDED_WPM_OPS
#define INCLUDED_WPM_OPS

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> struct is_shared_ptr : std::false_type {};

template <typename T>
struct is_shared_ptr<std::shared_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  return x ? std::make_unique<T>(x->clone()) : nullptr;
}

template <typename T>
std::shared_ptr<T> clone_value(const std::shared_ptr<T> &x) {
  return x ? std::make_shared<T>(x->clone()) : nullptr;
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using TargetBare = std::remove_cvref_t<Target>;
  using SourceBare = std::remove_cvref_t<Source>;
  if constexpr (is_unique_ptr<TargetBare>::value) {
    using Inner = typename is_unique_ptr<TargetBare>::element_type;
    if constexpr (is_unique_ptr<SourceBare>::value) {
      using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires {
                             typename Inner::crane_element_type;
                             x->template clone_as<
                                 typename Inner::crane_element_type>();
                           }) {
        return std::make_unique<Inner>(
            x->template clone_as<typename Inner::crane_element_type>());
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_unique<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x.clone());
      }
    }
  } else if constexpr (is_shared_ptr<TargetBare>::value) {
    using Inner = typename is_shared_ptr<TargetBare>::element_type;
    if constexpr (is_shared_ptr<SourceBare>::value) {
      using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else if constexpr (is_unique_ptr<SourceBare>::value) {
      if (!x)
        return nullptr;
      if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_shared<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x.clone());
      }
    }
  } else if constexpr (std::is_same_v<TargetBare, SourceBare>) {
    return clone_value(x);
  } else if constexpr (is_unique_ptr<SourceBare>::value) {
    using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (is_shared_ptr<SourceBare>::value) {
    using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (requires {
                         typename TargetBare::crane_element_type;
                         x.template clone_as<
                             typename TargetBare::crane_element_type>();
                       }) {
    return x.template clone_as<typename TargetBare::crane_element_type>();
  } else if constexpr (requires { x.template clone_as<TargetBare>(); }) {
    return x.template clone_as<TargetBare>();
  } else {
    return Target(x);
  }
}

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
      return List<t_A>(Cons{clone_as_value<t_A>(d_a0),
                            clone_as_value<std::unique_ptr<List<t_A>>>(d_a1)});
    }
  }

  template <typename _CloneT0>
  __attribute__((pure)) List<_CloneT0> clone_as() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<_CloneT0>(typename List<_CloneT0>::Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<_CloneT0>(typename List<_CloneT0>::Cons{
          clone_as_value<_CloneT0>(d_a0),
          clone_as_value<std::unique_ptr<List<_CloneT0>>>(d_a1)});
    }
  }

  // CREATORS
  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1.clone())});
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
};

struct ListDef {
  template <typename T1>
  static T1 nth(const unsigned int &n, const List<T1> &l, const T1 default0);
};

struct WpmOps {
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

  __attribute__((pure)) static bool nat_list_eqb(const List<unsigned int> &xs,
                                                 const List<unsigned int> &ys);

  struct state1 {
    List<unsigned int> rom1;
    unsigned int prom_addr1;
    unsigned int prom_data1;
    bool prom_enable1;

    __attribute__((pure)) state1 *operator->() { return this; }

    __attribute__((pure)) const state1 *operator->() const { return this; }
  };

  __attribute__((pure)) static state1 execute_wpm1(const state1 &s);
  static inline const state1 sample1 =
      state1{List<unsigned int>::cons(
                 10u, List<unsigned int>::cons(
                          11u, List<unsigned int>::cons(
                                   12u, List<unsigned int>::cons(
                                            13u, List<unsigned int>::nil())))),
             2u, 99u, false};
  static inline const state1 after1 = execute_wpm1(sample1);
  static inline const bool test_wpm_disabled_is_nop =
      (ListDef::template nth<unsigned int>(0u, after1.rom1, 0u) == 10u &&
       (ListDef::template nth<unsigned int>(1u, after1.rom1, 0u) == 11u &&
        (ListDef::template nth<unsigned int>(2u, after1.rom1, 0u) == 12u &&
         ListDef::template nth<unsigned int>(3u, after1.rom1, 0u) == 13u)));

  struct state2 {
    List<unsigned int> ram_sys2;
    List<unsigned int> rom2;
    unsigned int prom_addr2;
    unsigned int prom_data2;
    bool prom_enable2;

    __attribute__((pure)) state2 *operator->() { return this; }

    __attribute__((pure)) const state2 *operator->() const { return this; }
  };

  __attribute__((pure)) static state2 execute_wpm2(const state2 &s);
  static inline const state2 sample2 = state2{
      List<unsigned int>::cons(
          5u, List<unsigned int>::cons(
                  6u, List<unsigned int>::cons(7u, List<unsigned int>::nil()))),
      List<unsigned int>::cons(
          10u,
          List<unsigned int>::cons(
              11u, List<unsigned int>::cons(12u, List<unsigned int>::nil()))),
      1u, 99u, true};
  static inline const bool test_wpm_enabled_preserves_ram =
      nat_list_eqb(execute_wpm2(sample2).ram_sys2, sample2.ram_sys2);

  struct state3 {
    List<unsigned int> regs3;
    List<unsigned int> rom3;
    unsigned int prom_addr3;
    unsigned int prom_data3;
    bool prom_enable3;

    __attribute__((pure)) state3 *operator->() { return this; }

    __attribute__((pure)) const state3 *operator->() const { return this; }
  };

  __attribute__((pure)) static state3 execute_wpm3(const state3 &s);
  static inline const state3 sample3 = state3{
      List<unsigned int>::cons(
          1u, List<unsigned int>::cons(
                  2u, List<unsigned int>::cons(3u, List<unsigned int>::nil()))),
      List<unsigned int>::cons(
          10u,
          List<unsigned int>::cons(
              11u, List<unsigned int>::cons(12u, List<unsigned int>::nil()))),
      1u, 99u, true};
  static inline const bool test_wpm_enabled_preserves_regs =
      nat_list_eqb(execute_wpm3(sample3).regs3, sample3.regs3);

  struct state4 {
    List<unsigned int> rom4;
    unsigned int prom_addr4;
    unsigned int prom_data4;
    bool prom_enable4;

    __attribute__((pure)) state4 *operator->() { return this; }

    __attribute__((pure)) const state4 *operator->() const { return this; }
  };

  __attribute__((pure)) static state4 execute_wpm4(const state4 &s);
  static inline const unsigned int test_wpm_update_gate = []() {
    state4 s = state4{List<unsigned int>::cons(
                          10u, List<unsigned int>::cons(
                                   11u, List<unsigned int>::cons(
                                            12u, List<unsigned int>::nil()))),
                      1u, 99u, true};
    state4 s_ = execute_wpm4(s);
    return ListDef::template nth<unsigned int>(1u, s_.rom4, 0u);
  }();

  struct state5 {
    List<unsigned int> rom5;
    unsigned int prom_addr5;
    unsigned int prom_data5;
    bool prom_enable5;

    __attribute__((pure)) state5 *operator->() { return this; }

    __attribute__((pure)) const state5 *operator->() const { return this; }
  };

  __attribute__((pure)) static state5 execute_wpm5(const state5 &s);
  static inline const state5 sample5 =
      state5{List<unsigned int>::cons(
                 10u, List<unsigned int>::cons(
                          11u, List<unsigned int>::cons(
                                   12u, List<unsigned int>::cons(
                                            13u, List<unsigned int>::nil())))),
             2u, 99u, true};
  static inline const bool test_wpm_updates_rom_at_addr =
      ListDef::template nth<unsigned int>(2u, execute_wpm5(sample5).rom5, 0u) ==
      99u;

  struct state6 {
    List<unsigned int> rom6;
    unsigned int prom_addr6;
    unsigned int prom_data6;
    bool prom_enable6;

    __attribute__((pure)) state6 *operator->() { return this; }

    __attribute__((pure)) const state6 *operator->() const { return this; }
  };

  __attribute__((pure)) static state6 execute_wpm6(const state6 &s);
  static inline const state6 sample6 =
      state6{List<unsigned int>::cons(
                 10u, List<unsigned int>::cons(
                          11u, List<unsigned int>::cons(
                                   12u, List<unsigned int>::cons(
                                            13u, List<unsigned int>::nil())))),
             2u, 99u, true};
  static inline const state6 after6 = execute_wpm6(sample6);
  static inline const bool test_wpm_writes_exactly_once =
      (ListDef::template nth<unsigned int>(2u, after6.rom6, 0u) == 99u &&
       (ListDef::template nth<unsigned int>(0u, after6.rom6, 0u) == 10u &&
        (ListDef::template nth<unsigned int>(1u, after6.rom6, 0u) == 11u &&
         ListDef::template nth<unsigned int>(3u, after6.rom6, 0u) == 13u)));
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

#endif // INCLUDED_WPM_OPS
