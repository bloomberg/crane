#ifndef INCLUDED_STM
#define INCLUDED_STM

#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <mini_stm.h>
#include <type_traits>
#include <utility>
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

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  static std::unique_ptr<List<t_A>> nil_uptr() {
    return std::make_unique<List<t_A>>(Nil{});
  }

  static std::unique_ptr<List<t_A>>
  cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
    return std::make_unique<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::unique_ptr<List<t_A>> cons_uptr(t_A a0,
                                              std::shared_ptr<List<t_A>> &&a1) {
    return std::make_unique<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

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
                     return List<t_A>::cons(_args.d_a0, _args.d_a1->app(m));
                   }},
        this->v());
  }
};

struct STMDefs {
  template <typename T1, MapsTo<T1, T1> F1>
  static void modifyTVar(const std::shared_ptr<stm::TVar<T1>> a, F1 &&f);
};

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

  static unsigned int stm_basic_counter(const std::monostate _x);
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
  static unsigned int stm_orElse_retry_example(const std::monostate _x);
  static unsigned int io_orElse_retry_example();
};

template <typename T1, MapsTo<T1, T1> F1>
void STMDefs::modifyTVar(const std::shared_ptr<stm::TVar<T1>> a, F1 &&f) {
  T1 val = a->read();
  a->write(f(val));
  return;
}

#endif // INCLUDED_STM
