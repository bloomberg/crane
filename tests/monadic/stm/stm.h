#include <algorithm>
#include <any>
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
  template <typename A> struct list {
  public:
    struct nil {};
    struct cons {
      A _a0;
      std::shared_ptr<List::list<A>> _a1;
    };
    using variant_t = std::variant<nil, cons>;

  private:
    variant_t v_;
    explicit list(nil _v) : v_(std::move(_v)) {}
    explicit list(cons _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<List::list<A>> nil_() {
        return std::shared_ptr<List::list<A>>(new List::list<A>(nil{}));
      }
      static std::shared_ptr<List::list<A>>
      cons_(A a0, const std::shared_ptr<List::list<A>> &a1) {
        return std::shared_ptr<List::list<A>>(new List::list<A>(cons{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
    std::shared_ptr<List::list<A>>
    app(const std::shared_ptr<List::list<A>> &m) const {
      return std::visit(
          Overloaded{[&](const typename List::list<A>::nil _args)
                         -> std::shared_ptr<List::list<A>> { return m; },
                     [&](const typename List::list<A>::cons _args)
                         -> std::shared_ptr<List::list<A>> {
                       A a = _args._a0;
                       std::shared_ptr<List::list<A>> l1 = _args._a1;
                       return List::list<A>::ctor::cons_(a, l1->app(m));
                     }},
          this->v());
    }
  };
};

struct STM {};

struct TVar {};

template <typename T1, MapsTo<T1, T1> F1>
void modifyTVar(const std::shared_ptr<stm::TVar<T1>> a, F1 &&f) {
  T1 val0 = stm::readTVar<T1>(a);
  stm::writeTVar<T1>(a, f(val0));
  return;
}

struct stmtest {
  template <typename T1, MapsTo<bool, T1> F1>
  static T1 readOrRetry(const std::shared_ptr<stm::TVar<T1>> tv, F1 &&ok) {
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
                  stm::TVar<std::shared_ptr<List::list<unsigned int>>>>
                  q,
              const unsigned int x);

  static unsigned int
  stm_dequeue(const std::shared_ptr<
              stm::TVar<std::shared_ptr<List::list<unsigned int>>>>
                  q);

  static unsigned int
  stm_tryDequeue(const std::shared_ptr<
                     stm::TVar<std::shared_ptr<List::list<unsigned int>>>>
                     q,
                 const unsigned int dflt);

  static unsigned int stm_queue_roundtrip(const unsigned int x);

  static unsigned int io_queue_roundtrip(const unsigned int x);

  static unsigned int stm_orElse_retry_example();

  static unsigned int io_orElse_retry_example();
};
