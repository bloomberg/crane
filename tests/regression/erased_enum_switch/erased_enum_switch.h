#ifndef INCLUDED_ERASED_ENUM_SWITCH
#define INCLUDED_ERASED_ENUM_SWITCH

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <memory>
#include <utility>
#include <variant>

enum class Bool0;
struct Nat;
enum class Bool0 { TRUE_, FALSE_ };

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Nat() {}

  explicit Nat(O _v) : v_(_v) {}

  explicit Nat(S _v) : v_(std::move(_v)) {}

  static Nat o() { return Nat(O{}); }

  static Nat s(Nat a0) { return Nat(S{std::make_shared<Nat>(std::move(a0))}); }

  // MANIPULATORS
  ~Nat() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<Nat> {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      return nullptr;
    };
    std::shared_ptr<Nat> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  Nat(const Nat &) = default;
  Nat &operator=(const Nat &) = default;
  Nat(Nat &&) = default;
  Nat &operator=(Nat &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  Nat add(Nat m) const {
    std::shared_ptr<Nat> _head{};
    std::shared_ptr<Nat> *_write = &_head;
    const Nat *_loop_self = this;
    Nat _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        *_write = std::make_shared<Nat>(std::move(_loop_m));
        break;
      } else {
        const auto &[a0] = std::get<typename Nat::S>(_sv.v());
        auto _cell = std::make_shared<Nat>(typename Nat::S(nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename Nat::S>((*_write)->v_mut()).a0;
        _loop_self = crane_raw(a0);
        continue;
      }
    }
    return std::move(*_head);
  }
};

struct ErasedEnumSwitch {
  struct dep {
    // DATA
    crane::obj a;
    crane::fn<Nat(crane::obj)> a1;

    // ACCESSORS
    dep clone() const { return {a, a1}; }

    // CREATORS
    static dep d(crane::obj a, crane::fn<Nat(crane::obj)> a1) {
      return {std::move(a), std::move(a1)};
    }
  };

  template <typename T1, typename F0> static T1 dep_rect(F0 &&f, const dep &d) {
    const auto &[a0, a1] = d;
    return crane_any_cast<T1>(f(a0, a1));
  }

  template <typename T1, typename F0> static T1 dep_rec(F0 &&f, const dep &d) {
    const auto &[a0, a1] = d;
    return crane_any_cast<T1>(f(a0, a1));
  }

  static Nat run(const dep &d);
  static inline const Nat test =
      run(dep::d(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))),
                 crane::fn<Nat(crane::obj)>([](const crane::obj &n) -> Nat {
                   return crane::any_cast<Nat>(n);
                 })))
          .add(run(
              dep::d(Bool0::TRUE_,
                     crane::fn<Nat(crane::obj)>([](const crane::obj &b) -> Nat {
                       switch (crane::any_cast<Bool0>(b)) {
                       case Bool0::TRUE_: {
                         return Nat::s(Nat::o());
                       }
                       case Bool0::FALSE_: {
                         return Nat::o();
                       }
                       default:
                         std::unreachable();
                       }
                     }))));
};

#endif // INCLUDED_ERASED_ENUM_SWITCH
