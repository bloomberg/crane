#ifndef INCLUDED_STM
#define INCLUDED_STM

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <crane_itree.h>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <stm_adapter.h>
#include <system_error>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;

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

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_(crane_convert_spine(
            _other, std::shared_ptr<List<A>>(nullptr),
            [](const List<CraneU> &_cell) -> const List<CraneU> * {
              if (std::holds_alternative<typename List<CraneU>::Cons>(
                      _cell.v())) {
                return std::get<typename List<CraneU>::Cons>(_cell.v()).l.get();
              } else {
                return nullptr;
              }
            },
            [&](const List<CraneU> &_other,
                std::shared_ptr<List<A>> _below) -> variant_t {
              if (std::holds_alternative<typename List<CraneU>::Nil>(
                      _other.v())) {
                return Nil{};
              } else {
                const auto &[a, l] =
                    std::get<typename List<CraneU>::Cons>(_other.v());
                return Cons{
                    [&]() -> A {
                      if constexpr (crane_convertible<A, const CraneU &>) {
                        return crane_convert<A>(a);
                      } else {
                        throw std::logic_error(
                            "unreachable: inactive constructor field at this "
                            "instantiation");
                      }
                    }(),
                    std::move(_below)};
              }
            },
            [](auto &&_alt) {
              return std::make_shared<List<A>>(std::move(_alt));
            })) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) = default;
  List &operator=(List &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  List<A> app(List<A> m) const {
    std::optional<List<A>> _root{};
    std::shared_ptr<List<A>> *_write = nullptr;
    const List<A> *_loop_self = this;
    List<A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = std::move(_loop_m);
        (_write ? *(*_write = std::make_shared<List<A>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell = typename List<A>::Cons(a0, nullptr);
        List<A> &_node =
            (_write ? *(*_write = std::make_shared<List<A>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<A>::Cons>(_node.v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }
};

struct STMDefs {
  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, T1 &&>
  static void modifyTVar(stm::TVar<T1> a, F1 &&f);
};

struct stmtest {
  template <typename T1, typename F1>
  static T1 readOrRetry(stm::TVar<T1> tv, F1 &&ok) {
    T1 x = stm::readTVar(std::move(tv));
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
  requires std::is_invocable_r_v<T1, F1 &, T1 &&>
void STMDefs::modifyTVar(stm::TVar<T1> a, F1 &&f) {
  T1 val = stm::readTVar(a);
  stm::writeTVar(std::move(a), f(std::move(val)));
  return;
}

#endif // INCLUDED_STM
