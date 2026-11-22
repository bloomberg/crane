#pragma once

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
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
    requires std::is_invocable_r_v<T1, F0 &, T1 &&, const A &>
  T1 fold_left(F0 &&f, T1 a0) const {
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    const List<A> *_loop_self = this;
    T1 _loop_a0 = std::move(a0);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        return _loop_a0;
      } else {
        const auto &[a1, a2] = std::get<typename List<A>::Cons>(_sv.v());
        _loop_self = crane_raw(a2);
        _loop_a0 = f(std::move(_loop_a0), a1);
      }
    }
  }
};

struct CallableCrossingMatrix {
  static uint64_t add2(uint64_t x0_, uint64_t x1_);
  static uint64_t add3(uint64_t a, uint64_t b, uint64_t c);

  template <typename T1> static T1 idp(T1 x) { return x; }

  /// Slots.
  template <typename F0> static uint64_t at_param2(F0 &&f) {
    return f(UINT64_C(1), UINT64_C(2));
  }

  template <typename F0> static uint64_t at_param3(F0 &&f) {
    return f(UINT64_C(1), UINT64_C(2), UINT64_C(3));
  }

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, const F0 &, const uint64_t &,
                                   uint64_t &>
  static uint64_t at_tvar2(F0 &&f) {
    return idp<crane::fn<crane::fn<uint64_t(uint64_t)>(uint64_t)>>(
        [=](uint64_t _ec0) {
          return [=, f = f](uint64_t _ec1) { return f(_ec0, _ec1); };
        })(UINT64_C(1))(UINT64_C(2));
  }

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, const F0 &, const uint64_t &,
                                   const uint64_t &, uint64_t &>
  static uint64_t at_tvar3(F0 &&f) {
    return idp<
        crane::fn<crane::fn<crane::fn<uint64_t(uint64_t)>(uint64_t)>(uint64_t)>>(
        [=](uint64_t _ec0) {
          return [=, f = f](uint64_t _ec1) {
            return [=, f = f](uint64_t _ec2) { return f(_ec0, _ec1, _ec2); };
          };
        })(UINT64_C(1))(UINT64_C(2))(UINT64_C(3));
  }

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, const F0 &, const uint64_t &,
                                   uint64_t &>
  static uint64_t at_auto2(F0 &&f) {
    return crane::fn<crane::fn<uint64_t(uint64_t)>(uint64_t)>(
        [=](uint64_t _ec0) {
          return [=, f = f](uint64_t _ec1) { return f(_ec0, _ec1); };
        })(UINT64_C(1))(UINT64_C(2));
  }

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, const F0 &, const uint64_t &,
                                   const uint64_t &, uint64_t &>
  static uint64_t at_auto3(F0 &&f) {
    return crane::fn<
        crane::fn<crane::fn<uint64_t(uint64_t)>(uint64_t)>(uint64_t)>(
        [=](uint64_t _ec0) {
          return [=, f = f](uint64_t _ec1) {
            return [=, f = f](uint64_t _ec2) { return f(_ec0, _ec1, _ec2); };
          };
        })(UINT64_C(1))(UINT64_C(2))(UINT64_C(3));
  }

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, const F0 &, const uint64_t &,
                                   uint64_t &>
  static uint64_t at_loop2(F0 &&f) {
    return List<uint64_t>::cons(
        UINT64_C(1),
        List<uint64_t>::cons(UINT64_C(2),
                             List<uint64_t>::nil()))
               .template fold_left<
        crane::fn<crane::fn<uint64_t(uint64_t)>(uint64_t)>>(
        [](crane::fn<crane::fn<uint64_t(uint64_t)>(uint64_t)> g,
           uint64_t) { return g; },
        [=](uint64_t _ec0) {
          return [=, f = f](uint64_t _ec1) { return f(_ec0, _ec1); };
        })(UINT64_C(1))(UINT64_C(2));
  }

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, const F0 &, const uint64_t &,
                                   const uint64_t &, uint64_t &>
  static uint64_t at_loop3(F0 &&f) {
    return List<uint64_t>::cons(
        UINT64_C(1),
        List<uint64_t>::cons(UINT64_C(2),
                             List<uint64_t>::nil()))
               .template fold_left<
        crane::fn<crane::fn<crane::fn<uint64_t(uint64_t)>(uint64_t)>(uint64_t)>>(
        [](crane::fn<
            crane::fn<crane::fn<uint64_t(uint64_t)>(uint64_t)>(uint64_t)> g,
           uint64_t) { return g; },
        [=](uint64_t _ec0) {
          return [=, f = f](uint64_t _ec1) {
            return [=, f = f](uint64_t _ec2) { return f(_ec0, _ec1, _ec2); };
          };
        })(UINT64_C(1))(UINT64_C(2))(UINT64_C(3));
  }

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &, uint64_t &>
  static uint64_t at_return2(F0 &&f, uint64_t x0_, uint64_t x1_) {
    return f(x0_, x1_);
  }

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &, uint64_t &,
                                   uint64_t &>
  static uint64_t at_return3(F0 &&f, uint64_t x0_, uint64_t x1_, uint64_t x2_) {
    return f(x0_, x1_, x2_);
  }

  template <typename F0> static uint64_t at_let2(F0 &&f) {
    return at_param2(f);
  }

  template <typename F0> static uint64_t at_let3(F0 &&f) {
    return at_param3(f);
  }

  struct holder2 {
    crane::fn<uint64_t(uint64_t, uint64_t)> h2;
  };

  struct holder3 {
    crane::fn<uint64_t(uint64_t, uint64_t, uint64_t)> h3;
  };

  template <typename F0> static uint64_t at_field2(F0 &&f) {
    return at_param2(f);
  }

  template <typename F0> static uint64_t at_field3(F0 &&f) {
    return at_param3(f);
  }

  template <typename F0> static uint64_t at_erased2(F0 &&f) {
    return (UINT64_C(0) + f(UINT64_C(1), UINT64_C(2)));
  }

  /// Sources.
  static uint64_t curried2(uint64_t x0_, uint64_t x1_);
  static uint64_t curried3(uint64_t a, uint64_t b, uint64_t c);
  static uint64_t src_lambda2(uint64_t x0_, uint64_t x1_);
  static uint64_t src_let2(uint64_t n, uint64_t a, uint64_t b);
  static uint64_t src_match2(uint64_t n, uint64_t x0_, uint64_t x1_);
  static uint64_t src_fix2(uint64_t m, uint64_t a, uint64_t b);
  static uint64_t src_fix3(uint64_t m, uint64_t a, uint64_t b, uint64_t c);
  static uint64_t src_mapping2(uint64_t x0_, uint64_t x1_);

  template <typename F0> static uint64_t sum2(F0 &&slot) {
    return (
        (((((slot(add2) + slot(curried2)) + slot(src_lambda2)) +
           slot([](uint64_t _x0,
                   uint64_t _x1)
                     -> uint64_t { return src_let2(UINT64_C(0), _x0, _x1); })) +
          slot([](uint64_t _x0,
                  uint64_t _x1)
                    -> uint64_t {
            return src_match2(UINT64_C(0), _x0, _x1);
          })) +
         slot([](uint64_t _x0,
                 uint64_t _x1)
                   -> uint64_t { return src_fix2(UINT64_C(1), _x0, _x1); })) +
        slot(src_mapping2));
  }

  template <typename F0> static uint64_t sum3(F0 &&slot) {
    return (
        ((slot(add3) + slot(curried3)) +
         slot([](uint64_t a, uint64_t b,
                 uint64_t c) { return ((a + b) + c); })) +
        slot([](uint64_t _x0, uint64_t _x1,
                uint64_t _x2)
                  -> uint64_t {
          return src_fix3(UINT64_C(1), _x0, _x1, _x2);
        }));
  }

  static inline const uint64_t r2_param =
      sum2([](crane::fn<uint64_t(uint64_t,
                                 uint64_t)> _ec0) { return at_param2(_ec0); });
  static inline const uint64_t r2_tvar = sum2([](
      crane::fn<uint64_t(uint64_t, uint64_t)> _ec0) { return at_tvar2(_ec0); });
  static inline const uint64_t r2_auto = sum2([](
      crane::fn<uint64_t(uint64_t, uint64_t)> _ec0) { return at_auto2(_ec0); });
  static inline const uint64_t r2_loop = sum2([](
      crane::fn<uint64_t(uint64_t, uint64_t)> _ec0) { return at_loop2(_ec0); });
  static inline const uint64_t r2_return =
      sum2([](const crane::fn<uint64_t(uint64_t,
                                       uint64_t)> &f) {
        return at_return2(f, UINT64_C(1), UINT64_C(2));
      });
  static inline const uint64_t r2_let = sum2([](
      crane::fn<uint64_t(uint64_t, uint64_t)> _ec0) { return at_let2(_ec0); });
  static inline const uint64_t r2_field =
      sum2([](crane::fn<uint64_t(uint64_t,
                                 uint64_t)> _ec0) { return at_field2(_ec0); });
  static inline const uint64_t r2_erased =
      sum2([](crane::fn<uint64_t(uint64_t,
                                 uint64_t)> _ec0) { return at_erased2(_ec0); });
  static inline const uint64_t r3_param =
      sum3([](crane::fn<uint64_t(uint64_t, uint64_t,
                                 uint64_t)> _ec0) { return at_param3(_ec0); });
  static inline const uint64_t r3_tvar =
      sum3([](crane::fn<uint64_t(uint64_t, uint64_t,
                                 uint64_t)> _ec0) { return at_tvar3(_ec0); });
  static inline const uint64_t r3_auto =
      sum3([](crane::fn<uint64_t(uint64_t, uint64_t,
                                 uint64_t)> _ec0) { return at_auto3(_ec0); });
  static inline const uint64_t r3_loop =
      sum3([](crane::fn<uint64_t(uint64_t, uint64_t,
                                 uint64_t)> _ec0) { return at_loop3(_ec0); });
  static inline const uint64_t r3_return =
      sum3([](const crane::fn<uint64_t(uint64_t, uint64_t,
                                       uint64_t)> &f) {
        return at_return3(f, UINT64_C(1), UINT64_C(2), UINT64_C(3));
      });
  static inline const uint64_t r3_let =
      sum3([](crane::fn<uint64_t(uint64_t, uint64_t,
                                 uint64_t)> _ec0) { return at_let3(_ec0); });
  static inline const uint64_t r3_field =
      sum3([](crane::fn<uint64_t(uint64_t, uint64_t,
                                 uint64_t)> _ec0) { return at_field3(_ec0); });
};
