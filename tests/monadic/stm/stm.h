#include <algorithm>
#include <fstream>
#include <functional>
#include <iostream>
#include <memory>
#include <mini_stm.h>
#include <optional>
#include <string>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct List {
  template <typename A> struct nil;
  template <typename A> struct cons;
  template <typename A> using list = std::variant<nil<A>, cons<A>>;
  template <typename A> struct nil {
    static std::shared_ptr<list<A>> make() {
      return std::make_shared<list<A>>(nil<A>{});
    }
  };
  template <typename A> struct cons {
    A _a0;
    std::shared_ptr<list<A>> _a1;
    static std::shared_ptr<list<A>> make(A _a0, std::shared_ptr<list<A>> _a1) {
      return std::make_shared<list<A>>(cons<A>{_a0, _a1});
    }
  };
};

template <typename T1>
std::shared_ptr<typename List::list<T1>>
app(const std::shared_ptr<typename List::list<T1>> l,
    const std::shared_ptr<typename List::list<T1>> m) {
  return std::visit(
      Overloaded{[&](const typename List::nil<T1> _args)
                     -> std::shared_ptr<typename List::list<T1>> { return m; },
                 [&](const typename List::cons<T1> _args)
                     -> std::shared_ptr<typename List::list<T1>> {
                   T1 a = _args._a0;
                   std::shared_ptr<typename List::list<T1>> l1 = _args._a1;
                   return List::cons<T1>::make(a, app<T1>(l1, m));
                 }},
      *l);
}

template <typename T1, MapsTo<T1, T1> F1>
void modifyTVar(const std::shared_ptr<stm::TVar<T1>> a, F1 &&f) {
  T1 val0 = stm::readTVar<T1>(a);
  stm::writeTVar<T1>(a, f(val0));
  return;
}

struct stmtest {
  template <typename T1, MapsTo<bool, T1> F1>
  T1 readOrRetry(const std::shared_ptr<stm::TVar<T1>> tv, F1 &&ok) {
    T1 x = stm::readTVar<T1>(tv);
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

  static void
  stm_enqueue(const std::shared_ptr<
                  stm::TVar<std::shared_ptr<typename List::list<unsigned int>>>>
                  q,
              const unsigned int x);

  static unsigned int
  stm_dequeue(const std::shared_ptr<
              stm::TVar<std::shared_ptr<typename List::list<unsigned int>>>>
                  q);

  static unsigned int stm_tryDequeue(
      const std::shared_ptr<
          stm::TVar<std::shared_ptr<typename List::list<unsigned int>>>>
          q,
      const unsigned int dflt);

  static unsigned int stm_queue_roundtrip(const unsigned int x);

  static unsigned int io_queue_roundtrip(const unsigned int x);

  static unsigned int stm_orElse_retry_example();

  static unsigned int io_orElse_retry_example();
};
