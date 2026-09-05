#ifndef INCLUDED_TYPE_LEVEL_TUPLE_FIXPOINT
#define INCLUDED_TYPE_LEVEL_TUPLE_FIXPOINT

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
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

struct TypeLevelTupleFixpoint {
  /// A Fixpoint returning a Type built from tuples.  tup 3 is a concrete
  /// nested std::pair at every use site, but Crane erases it to std::any and
  /// then reads through it:
  ///
  /// error: no viable conversion from returned value of type 'std::any'
  /// to function return type 'Nat'
  ///
  /// Unlike type_level_fixpoint_call, the computed type is a *tuple*, not a
  /// function type.
  using tup = std::any;
  static inline const tup mk3 = std::make_pair(
      std::any(Nat::s(Nat::o())),
      std::any(std::make_pair(
          std::any(Nat::s(Nat::s(Nat::o()))),
          std::any(std::make_pair(std::any(Nat::s(Nat::s(Nat::s(Nat::o())))),
                                  std::any(std::monostate{}))))));
  static Nat fst3(tup t);
  static inline const Nat run = fst3(mk3);
};

#endif // INCLUDED_TYPE_LEVEL_TUPLE_FIXPOINT
