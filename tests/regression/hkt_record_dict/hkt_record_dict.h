#ifndef INCLUDED_HKT_RECORD_DICT
#define INCLUDED_HKT_RECORD_DICT

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
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

/// The same higher-kinded signature as a Record rather than a Class.  The
/// record's parameter is emitted as a plain typename F but its field type is
/// spelled F<std::any>, and the accessor treats the dictionary *value* as a
/// scope (f::template fmd<...>).
struct HktRecordDict {
  template <typename F> struct FnD {
    crane::fn<F(crane::fn<crane::obj(crane::obj)>, F)> fmd;

    // ACCESSORS
    template <typename CraneU> operator FnD<CraneU>() const {
      return {crane_convert<
          crane::fn<CraneU(crane::fn<crane::obj(crane::obj)>, CraneU)>>(fmd)};
    }
  };

  template <template <typename> class T1, typename T2, typename F1,
            typename T3 = std::invoke_result_t<F1 &, T2 &>>
  static T1<T3> fmd(const FnD<T1<crane::obj>> &f, F1 &&x, T1<T2> x0) {
    return crane_container_cast<T1<T3>>(
        f.fmd(crane_erase_fn(x),
              crane_container_cast<T1<crane::obj>>(std::move(x0))));
  }

  static inline const FnD<std::optional<crane::obj>> optd =
      FnD<std::optional<crane::obj>>{
          []<typename CraneX>(
              const crane::fn<CraneX(CraneX)> &f,
              const std::optional<CraneX> &o) -> std::optional<crane::obj> {
            if (o.has_value()) {
              const auto &x = *o;
              return std::make_optional<CraneX>(
                  CraneX(crane_call_erased(f, x)));
            } else {
              return std::optional<CraneX>();
            }
          }};
  static inline const std::optional<Nat> ex = fmd<std::optional>(
      optd, [](const Nat &x) { return Nat::s(x); },
      std::make_optional<Nat>(Nat::s(Nat::o())));
};

#endif // INCLUDED_HKT_RECORD_DICT
