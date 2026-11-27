#pragma once

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <typed_mapping_access_support.h>
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
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, crane::shared_child_slot<List<A>> l) {
    return List<A>(Cons{std::move(a), l.take()});
  }

  // MANIPULATORS
  ~List() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
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

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const A &>
  List<T1> map(F0 &&f) const {
    // Builds the result front to back: _write points at the empty tail the next
    // cell fills.
    std::optional<List<T1>> _root{};
    std::shared_ptr<List<T1>> *_write = nullptr;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = List<T1>::nil();
        (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell = typename List<T1>::Cons(f(a0), nullptr);
        List<T1> &_node =
            (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<T1>::Cons>(_node.v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }
};

struct TypedMappingAccess {
  /// Reads only: the canonical read form.
  static uint64_t peek(const access_support::handle &x0_);
  /// Writes through the handle, two calls deep.
  static access_support::handle poke(const access_support::handle &x0_,
                                     uint64_t x1_);
  static access_support::handle poke_middle(const access_support::handle &h,
                                            uint64_t n);
  static uint64_t poke_outer(const access_support::handle &h, uint64_t n);
  /// Reseats the handle, two calls deep.
  static uint64_t reseat(access_support::handle &h, uint64_t n);
  static uint64_t reseat_outer(access_support::handle &h, uint64_t n);
  /// Keeps the handle: owned, by value, even though it is reseated too.
  static access_support::handle keep(access_support::handle x0_);
  static uint64_t keep_and_reseat(access_support::handle h);
  /// Writes the buffer in place, two calls deep.
  static uint64_t buf_size(const access_support::buf &x0_);
  static access_support::buf push(access_support::buf &x0_, uint64_t x1_);
  static access_support::buf push_middle(access_support::buf &b);
  static uint64_t push_outer(access_support::buf &b);
  /// A recursive group: ping reseats, pong only passes its handle to
  /// ping, and is first in the group.
  static uint64_t pong(access_support::handle &h, uint64_t n);
  static uint64_t ping(access_support::handle &h, uint64_t n);

  /// reseat_value is passed as a value: it keeps the canonical ABI.
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &,
                                   const access_support::handle &>
  static uint64_t apply_handle(F0 &&f, const access_support::handle &x0_) {
    return f(x0_);
  }

  static uint64_t reseat_value(access_support::handle h);
  static uint64_t through_value(const access_support::handle &h);
  /// A value that is not a variable, passed where the callee replaces or
  /// writes it in place, is materialised for the call.
  static uint64_t reseat_fresh(uint64_t n);
  static uint64_t reseat_fresh_op(uint64_t n);
  static uint64_t push_fresh(uint64_t n);
  /// Self recursion: in a loop, and through a stack of frames
  /// (Crane Loopify is set).
  static uint64_t reseat_loop(access_support::handle &h, uint64_t n);
  static uint64_t push_loop(access_support::buf &b, uint64_t n);
  static uint64_t reseat_sum(access_support::handle &h, uint64_t n);
  static uint64_t reseat_each(access_support::handle &h,
                              const List<uint64_t> &l);
  static uint64_t push_each(access_support::buf &b, const List<uint64_t> &l);
  static List<uint64_t> push_all(access_support::buf &b,
                                 const List<uint64_t> &l);
  static uint64_t reseat_down(access_support::handle &h,
                              const List<uint64_t> &l);
  /// In a closure: the lambda's own parameter, and a captured one.
  static List<uint64_t>
  reseat_each_value(const List<access_support::handle> &l);
  static List<uint64_t> reseat_captured(const access_support::handle &h,
                                        const List<uint64_t> &l);
};
