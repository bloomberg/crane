#ifndef INCLUDED_ROCQ_BUG_7228
#define INCLUDED_ROCQ_BUG_7228

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat;

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
};

struct RocqBug7228 {
  struct data {
    // DATA
    crane::obj t;

    // ACCESSORS
    data clone() const { return {t}; }

    // CREATORS
    static data data0(crane::obj t) { return {std::move(t)}; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, crane::obj &>
  static T1 data_rect(F0 &&f, const data &d) {
    const auto &[t0] = d;
    return crane_any_cast<T1>(f(t0));
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, crane::obj &>
  static T1 data_rec(F0 &&f, const data &d) {
    const auto &[t0] = d;
    return crane_any_cast<T1>(f(t0));
  }

  using t_of = crane::obj;
  static t_of v_of(const data &d);
  static inline const data test_data =
      data::data0(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
          Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
              Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                  Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                      Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                          Nat::o())))))))))))))))))))))))))))))))))))))))))));
};

#endif // INCLUDED_ROCQ_BUG_7228
