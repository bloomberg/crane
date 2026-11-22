#pragma once

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <bsl_concepts.h>
#include <bsl_functional.h>
#include <bsl_iostream.h>
#include <bsl_memory.h>
#include <bsl_stdexcept.h>
#include <bsl_string.h>
#include <bsl_type_traits.h>
#include <bsl_variant.h>
#include <bsl_vector.h>
#include <utility>

using namespace BloombergLP;
template <class From, class To>
concept convertible_to = bsl::is_convertible<From, To>::value;

template <class T, class U>
concept same_as = bsl::is_same<T, U>::value && bsl::is_same<U, T>::value;

template <typename t_A> struct List;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a;
    bsl::shared_ptr<List<t_A>> d_l;
  };

  using variant_t = bsl::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(bsl::move(_v)) {}

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : d_v_([&]() -> variant_t {
          if (bsl::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[d_a, d_l] =
                bsl::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> t_A {
                  if constexpr (crane_convertible<t_A, const CraneU &>) {
                    return crane_convert<t_A>(d_a);
                  } else {
                    throw bsl::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (d_l ? bsl::make_shared<List<t_A>>(
                           crane_convert<List<t_A>>(*d_l))
                     : nullptr)};
          }
        }()) {}

  static List<t_A> nil() { return List<t_A>(Nil{}); }

  static List<t_A> cons(t_A a, List<t_A> l) {
    return List<t_A>(
        Cons{bsl::move(a), bsl::make_shared<List<t_A>>(bsl::move(l))});
  }

  // MANIPULATORS
  ~List() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
    auto _next = [&](variant_t &_v) -> bsl::shared_ptr<List<t_A>> {
      if (auto *_alt = bsl::get_if<Cons>(&_v)) {
        if (_alt->d_l && _alt->d_l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return bsl::move(_alt->d_l);
        }
      }
      return nullptr;
    };
    bsl::shared_ptr<List<t_A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) = default;
  List &operator=(List &&) = default;

  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }

  template <typename T1, typename F0>
    requires bsl::is_invocable_r_v<T1, F0 &, T1 &&, const t_A &>
  T1 fold_left(F0 &&f, T1 a0) const {
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    const List<t_A> *_loop_self = this;
    T1 _loop_a0 = bsl::move(a0);
    while (true) {
      auto &&_sv = *_loop_self;
      if (bsl::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
        return _loop_a0;
      } else {
        const auto &[d_a0, d_a1] = bsl::get<typename List<t_A>::Cons>(_sv.v());
        _loop_self = crane_raw(d_a1);
        _loop_a0 = f(bsl::move(_loop_a0), d_a0);
      }
    }
  }

  List<t_A> app(List<t_A> m) const {
    // Builds the result front to back: _write points at the empty tail the next
    // cell fills.
    bsl::optional<List<t_A>> _root{};
    bsl::shared_ptr<List<t_A>> *_write = nullptr;
    const List<t_A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (bsl::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
        auto _value = bsl::move(m);
        (_write ? *(*_write = bsl::make_shared<List<t_A>>(bsl::move(_value)))
                : _root.emplace(bsl::move(_value)));
        break;
      } else {
        const auto &[d_a0, d_a1] = bsl::get<typename List<t_A>::Cons>(_sv.v());
        auto _cell = typename List<t_A>::Cons(d_a0, nullptr);
        List<t_A> &_node =
            (_write ? *(*_write = bsl::make_shared<List<t_A>>(bsl::move(_cell)))
                    : _root.emplace(bsl::move(_cell)));
        _write = &bsl::get<typename List<t_A>::Cons>(_node.v_mut()).d_l;
        _loop_self = crane_raw(d_a1);
        continue;
      }
    }
    return bsl::move(*_root);
  }
};

struct TmcOptionalBde {
  static inline const List<unsigned int> joined =
      List<unsigned int>::cons(
          1u, List<unsigned int>::cons(2u, List<unsigned int>::nil()))
          .app(List<unsigned int>::cons(3u, List<unsigned int>::nil()));
  static inline const unsigned int total =
      joined.template fold_left<unsigned int>(
          [](unsigned int _x0,
             unsigned int _x1)
               -> unsigned int { return (_x0 + _x1); },
          0u);
};
