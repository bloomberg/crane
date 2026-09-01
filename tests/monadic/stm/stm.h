#ifndef INCLUDED_STM
#define INCLUDED_STM

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <stm_adapter.h>
#include <system_error>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename _U> List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    crane::small_vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        std::atomic_thread_fence(std::memory_order_acquire);
        _drain(_cur->v_mut());
      }
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  List<A> app(List<A> m) const {
    std::shared_ptr<List<A>> _head{};
    std::shared_ptr<List<A>> *_write = &_head;
    const List<A> *_loop_self = this;
    List<A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        *_write = std::make_shared<List<A>>(std::move(_loop_m));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell =
            std::make_shared<List<A>>(typename List<A>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<A>::Cons>((*_write)->v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_head);
  }
};

struct STMDefs {
  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, T1 &>
  static void modifyTVar(stm::TVar<T1> a, F1 &&f);
};

struct stmtest {
  template <typename T1, typename F1>
    requires std::is_invocable_r_v<bool, F1 &, T1 &>
  static T1 readOrRetry(stm::TVar<T1> tv, F1 &&ok) {
    T1 x = stm::readTVar(tv);
    if (ok(x)) {
      return x;
    } else {
      return stm::retry<T1>();
    }
  }

  static uint64_t stm_basic_counter(std::monostate _x);
  static uint64_t io_basic_counter();
  static uint64_t stm_inc(uint64_t x);
  static uint64_t io_inc(uint64_t x);
  static uint64_t stm_add_self(uint64_t x);
  static uint64_t io_add_self(uint64_t x);
  static void stm_enqueue(stm::TVar<List<uint64_t>> q, uint64_t x);
  static uint64_t stm_dequeue(stm::TVar<List<uint64_t>> q);
  static uint64_t stm_tryDequeue(stm::TVar<List<uint64_t>> q, uint64_t dflt);
  static uint64_t stm_queue_roundtrip(uint64_t x);
  static uint64_t io_queue_roundtrip(uint64_t x);
  static uint64_t stm_orElse_retry_example(std::monostate _x);
  static uint64_t io_orElse_retry_example();
};

template <typename T1, typename F1>
  requires std::is_invocable_r_v<T1, F1 &, T1 &>
void STMDefs::modifyTVar(stm::TVar<T1> a, F1 &&f) {
  T1 val = stm::readTVar(a);
  stm::writeTVar(a, f(val));
  return;
}

#endif // INCLUDED_STM
