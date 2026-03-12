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

template <typename A> struct List {
  // TYPES
  struct nil {};

  struct cons {
    A _a0;
    std::shared_ptr<List<A>> _a1;
  };

  using variant_t = std::variant<nil, cons>;

private:
  // DATA
  variant_t v_;

  // CREATORS
  explicit List(nil _v) : v_(std::move(_v)) {}

  explicit List(cons _v) : v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<A>> nil_() {
      return std::shared_ptr<List<A>>(new List<A>(nil{}));
    }

    static std::shared_ptr<List<A>> cons_(A a0,
                                          const std::shared_ptr<List<A>> &a1) {
      return std::shared_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }

    static std::unique_ptr<List<A>> nil_uptr() {
      return std::unique_ptr<List<A>>(new List<A>(nil{}));
    }

    static std::unique_ptr<List<A>>
    cons_uptr(A a0, const std::shared_ptr<List<A>> &a1) {
      return std::unique_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
  };

  // MANIPULATORS
  variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  std::shared_ptr<List<A>> app(std::shared_ptr<List<A>> m) const {
    return std::visit(Overloaded{[&](const typename List<A>::nil _args)
                                     -> std::shared_ptr<List<A>> { return m; },
                                 [&](const typename List<A>::cons _args)
                                     -> std::shared_ptr<List<A>> {
                                   A a = _args._a0;
                                   std::shared_ptr<List<A>> l1 = _args._a1;
                                   return List<A>::ctor::cons_(
                                       a, std::move(l1)->app(m));
                                 }},
                      this->v());
  }
};

struct STM {};

struct TVar {};

template <typename T1, MapsTo<T1, T1> F1>
void modifyTVar(const std::shared_ptr<stm::TVar<T1>> a, F1 &&f) {
  T1 val = a->read();
  a->write(f(val));
  return;
}

struct stmtest {
  template <typename T1, MapsTo<bool, T1> F1>
  static T1 readOrRetry(const std::shared_ptr<stm::TVar<T1>> tv, F1 &&ok) {
    T1 x = tv->read();
    if (ok(x)) {
      return x;
    } else {
      return stm::retry<T1>();
    }
  }

  static unsigned int stm_basic_counter();
  static unsigned int io_basic_counter();
  static unsigned int stm_inc(const unsigned int x);
  static unsigned int io_inc(const unsigned int x);
  static unsigned int stm_add_self(const unsigned int x);
  static unsigned int io_add_self(const unsigned int x);
  static void stm_enqueue(
      const std::shared_ptr<stm::TVar<std::shared_ptr<List<unsigned int>>>> q,
      const unsigned int x);
  static unsigned int stm_dequeue(
      const std::shared_ptr<stm::TVar<std::shared_ptr<List<unsigned int>>>> q);
  static unsigned int stm_tryDequeue(
      const std::shared_ptr<stm::TVar<std::shared_ptr<List<unsigned int>>>> q,
      const unsigned int dflt);
  static unsigned int stm_queue_roundtrip(const unsigned int x);
  static unsigned int io_queue_roundtrip(const unsigned int x);
  static unsigned int stm_orElse_retry_example();
  static unsigned int io_orElse_retry_example();
};
