#ifndef INCLUDED_STM
#define INCLUDED_STM

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <mini_stm.h>
#include <optional>
#include <stdexcept>
#include <string>
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

  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<t_A>> Nil_() {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::shared_ptr<List<t_A>>
    Cons_(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }

    static std::unique_ptr<List<t_A>> Nil_uptr() {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::unique_ptr<List<t_A>>
    Cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  std::shared_ptr<List<t_A>> app(std::shared_ptr<List<t_A>> m) const {
    return std::visit(
        Overloaded{[&](const typename List<t_A>::Nil _args)
                       -> std::shared_ptr<List<t_A>> { return m; },
                   [&](const typename List<t_A>::Cons _args)
                       -> std::shared_ptr<List<t_A>> {
                     t_A a = _args.d_a0;
                     std::shared_ptr<List<t_A>> l1 = _args.d_a1;
                     return List<t_A>::ctor::Cons_(a, std::move(l1)->app(m));
                   }},
        this->v());
  }
};

struct STM {};

struct TVar {};

template <typename T1, MapsTo<T1, T1> F1>
__attribute__((pure)) void modifyTVar(const std::shared_ptr<stm::TVar<T1>> a,
                                      F1 &&f) {
  T1 val = a->read();
  a->write(f(val));
  return;
}

struct stmtest {
  template <typename T1, MapsTo<bool, T1> F1>
  __attribute__((pure)) static T1
  readOrRetry(const std::shared_ptr<stm::TVar<T1>> tv, F1 &&ok) {
    T1 x = tv->read();
    if (ok(x)) {
      return x;
    } else {
      return stm::retry<T1>();
    }
  }

  __attribute__((pure)) static unsigned int stm_basic_counter();
  __attribute__((pure)) static unsigned int io_basic_counter();
  __attribute__((pure)) static unsigned int stm_inc(const unsigned int x);
  __attribute__((pure)) static unsigned int io_inc(const unsigned int x);
  __attribute__((pure)) static unsigned int stm_add_self(const unsigned int x);
  __attribute__((pure)) static unsigned int io_add_self(const unsigned int x);
  __attribute__((pure)) static void stm_enqueue(
      const std::shared_ptr<stm::TVar<std::shared_ptr<List<unsigned int>>>> q,
      const unsigned int x);
  __attribute__((pure)) static unsigned int stm_dequeue(
      const std::shared_ptr<stm::TVar<std::shared_ptr<List<unsigned int>>>> q);
  __attribute__((pure)) static unsigned int stm_tryDequeue(
      const std::shared_ptr<stm::TVar<std::shared_ptr<List<unsigned int>>>> q,
      const unsigned int dflt);
  __attribute__((pure)) static unsigned int
  stm_queue_roundtrip(const unsigned int x);
  __attribute__((pure)) static unsigned int
  io_queue_roundtrip(const unsigned int x);
  __attribute__((pure)) static unsigned int stm_orElse_retry_example();
  __attribute__((pure)) static unsigned int io_orElse_retry_example();
};

#endif // INCLUDED_STM
