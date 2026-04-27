#ifndef INCLUDED_STM
#define INCLUDED_STM

#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
#include <stm_adapter.h>
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

  __attribute__((pure)) List<t_A> app(List<t_A> m) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return m;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return List<t_A>::cons(d_a0, (*(d_a1)).app(m));
    }
  }
};

struct STMDefs {
  template <typename T1, MapsTo<T1, T1> F1>
  static void modifyTVar(const stm::TVar<T1> a, F1 &&f);
};

struct stmtest {
  template <typename T1, MapsTo<bool, T1> F1>
  static T1 readOrRetry(const stm::TVar<T1> tv, F1 &&ok) {
    T1 x = stm::readTVar(tv);
    if (ok(x)) {
      return x;
    } else {
      return stm::retry<T1>();
    }
  }

  static unsigned int stm_basic_counter(const std::monostate &_x);
  static unsigned int io_basic_counter();
  static unsigned int stm_inc(const unsigned int &x);
  static unsigned int io_inc(const unsigned int &x);
  static unsigned int stm_add_self(unsigned int x);
  static unsigned int io_add_self(const unsigned int &x);
  static void stm_enqueue(const stm::TVar<List<unsigned int>> q,
                          unsigned int x);
  static unsigned int stm_dequeue(const stm::TVar<List<unsigned int>> q);
  static unsigned int stm_tryDequeue(const stm::TVar<List<unsigned int>> q,
                                     const unsigned int &dflt);
  static unsigned int stm_queue_roundtrip(unsigned int x);
  static unsigned int io_queue_roundtrip(const unsigned int &x);
  static unsigned int stm_orElse_retry_example(const std::monostate &_x);
  static unsigned int io_orElse_retry_example();
};

template <typename T1, MapsTo<T1, T1> F1>
void STMDefs::modifyTVar(const stm::TVar<T1> a, F1 &&f) {
  T1 val = stm::readTVar(a);
  stm::writeTVar(a, f(val));
  return;
}

#endif // INCLUDED_STM
