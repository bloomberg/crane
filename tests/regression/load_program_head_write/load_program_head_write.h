#ifndef INCLUDED_LOAD_PROGRAM_HEAD_WRITE
#define INCLUDED_LOAD_PROGRAM_HEAD_WRITE

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

struct LoadProgramHeadWrite {
  struct state {
    List<unsigned int> rom;
    unsigned int prom_addr;
    unsigned int prom_data;
    bool prom_enable;

    __attribute__((pure)) state *operator->() { return this; }

    __attribute__((pure)) const state *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) state clone() const {
      return state{(*(this)).rom.clone(), (*(this)).prom_addr,
                   (*(this)).prom_data, (*(this)).prom_enable};
    }
  };

  __attribute__((pure)) static List<unsigned int>
  update_nth(const unsigned int &n, unsigned int x, List<unsigned int> l);
  __attribute__((pure)) static state set_prom_params(const state &s,
                                                     unsigned int addr,
                                                     unsigned int data,
                                                     bool enable);
  __attribute__((pure)) static state execute_wpm(const state &s);
  __attribute__((pure)) static state
  load_program(state s, const unsigned int &base,
               const List<unsigned int> &bytes);
  static inline const unsigned int t = []() {
    state s0 =
        state{List<unsigned int>::cons(
                  0u, List<unsigned int>::cons(
                          0u, List<unsigned int>::cons(
                                  0u, List<unsigned int>::cons(
                                          0u, List<unsigned int>::nil())))),
              0u, 0u, false};
    state s1 = load_program(
        s0, 1u,
        List<unsigned int>::cons(
            7u, List<unsigned int>::cons(8u, List<unsigned int>::nil())));
    return ListDef::template nth<unsigned int>(1u, s1.rom, 0u);
  }();
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

#endif // INCLUDED_LOAD_PROGRAM_HEAD_WRITE
