#ifndef INCLUDED_RESET_STATE
#define INCLUDED_RESET_STATE

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

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
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
      return List<t_A>(Cons{
          d_a0, d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

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

struct ResetState {
  struct state_full {
    unsigned int acc;
    List<unsigned int> regs_full;
    bool carry;
    unsigned int pc_full;
    List<unsigned int> stack;
    List<unsigned int> ram_sys;
    List<unsigned int> rom;

    // ACCESSORS
    __attribute__((pure)) state_full clone() const {
      return state_full{(*(this)).acc,           (*(this)).regs_full.clone(),
                        (*(this)).carry,         (*(this)).pc_full,
                        (*(this)).stack.clone(), (*(this)).ram_sys.clone(),
                        (*(this)).rom.clone()};
    }
  };

  struct state_minimal {
    List<unsigned int> regs_minimal;
    bool carry_minimal;
    unsigned int pc_minimal;
    List<unsigned int> ram_sys_minimal;
    List<unsigned int> rom_minimal;

    // ACCESSORS
    __attribute__((pure)) state_minimal clone() const {
      return state_minimal{(*(this)).regs_minimal.clone(),
                           (*(this)).carry_minimal, (*(this)).pc_minimal,
                           (*(this)).ram_sys_minimal.clone(),
                           (*(this)).rom_minimal.clone()};
    }
  };

  __attribute__((pure)) static state_full reset_state_full(const state_full &s);
  static inline const unsigned int memory_preserve_test = []() {
    state_full s = state_full{
        9u,
        List<unsigned int>::cons(
            1u, List<unsigned int>::cons(2u, List<unsigned int>::nil())),
        true,
        55u,
        List<unsigned int>::cons(
            8u, List<unsigned int>::cons(7u, List<unsigned int>::nil())),
        List<unsigned int>::cons(
            3u,
            List<unsigned int>::cons(
                4u, List<unsigned int>::cons(5u, List<unsigned int>::nil()))),
        List<unsigned int>::cons(
            10u, List<unsigned int>::cons(11u, List<unsigned int>::nil()))};
    state_full s_ = reset_state_full(s);
    return (
        ((s_.acc + ListDef::template nth<unsigned int>(1u, s_.ram_sys, 0u)) +
         ListDef::template nth<unsigned int>(0u, s_.rom, 0u)) +
        s_.stack.length());
  }();
  __attribute__((pure)) static state_minimal
  reset_state_minimal(const state_minimal &s);
  static inline const unsigned int pc_clear_test =
      reset_state_minimal(
          state_minimal{
              List<unsigned int>::cons(
                  1u, List<unsigned int>::cons(2u, List<unsigned int>::nil())),
              true, 99u,
              List<unsigned int>::cons(3u, List<unsigned int>::nil()),
              List<unsigned int>::cons(
                  4u, List<unsigned int>::cons(5u, List<unsigned int>::nil()))})
          .pc_minimal;
  static inline const std::pair<unsigned int, unsigned int> t =
      std::make_pair(memory_preserve_test, pc_clear_test);
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

#endif // INCLUDED_RESET_STATE
