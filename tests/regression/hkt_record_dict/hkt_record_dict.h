#ifndef INCLUDED_HKT_RECORD_DICT
#define INCLUDED_HKT_RECORD_DICT

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <functional>
#include <memory>
#include <optional>
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
    crane::small_vector<std::shared_ptr<Nat>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
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

  Nat(const Nat &) = default;
  Nat &operator=(const Nat &) = default;
  Nat(Nat &&) noexcept = default;
  Nat &operator=(Nat &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

/// The same higher-kinded signature as a Record rather than a Class.  The
/// record's parameter is emitted as a plain typename F but its field type is
/// spelled F<std::any>, and the accessor treats the dictionary *value* as a
/// scope (f::template fmd<...>).
struct HktRecordDict {
  template <typename F> struct FnD {
    std::function<F(std::function<std::any(std::any)>, F)> fmd;
  };

  template <template <typename> class T1, typename T2, typename F1,
            typename T3 = std::invoke_result_t<F1 &, T2 &>>
  static T1<T3> fmd(const FnD<T1<std::any>> &f, F1 &&x, T1<T2> x0) {
    return crane_container_cast<T1<T3>>(f.fmd(
        crane_erase_fn(x), crane_container_cast<T1<std::any>>(std::move(x0))));
  }

  static inline const FnD<std::optional<std::any>> optd =
      FnD<std::optional<std::any>>{[](const auto &f, const auto &o) {
        if (o.has_value()) {
          const auto &x = *o;
          return std::make_optional<std::any>(
              std::any(crane_call_erased(f, x)));
        } else {
          return std::optional<std::any>();
        }
      }};
  static inline const std::optional<Nat> ex = fmd(
      optd, [](Nat x) { return Nat::s(x); },
      std::make_optional<Nat>(Nat::s(Nat::o())));
};

#endif // INCLUDED_HKT_RECORD_DICT
