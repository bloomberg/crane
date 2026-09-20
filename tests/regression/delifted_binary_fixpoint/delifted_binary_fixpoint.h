#ifndef INCLUDED_DELIFTED_BINARY_FIXPOINT
#define INCLUDED_DELIFTED_BINARY_FIXPOINT

#include "small_vector.h"
#include <atomic>
#include <memory>
#include <utility>
#include <variant>

struct Positive;

struct Positive {
  // TYPES
  struct XI {
    std::shared_ptr<Positive> a0;
  };

  struct XO {
    std::shared_ptr<Positive> a0;
  };

  struct XH {};

  using variant_t = std::variant<XI, XO, XH>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Positive() {}

  explicit Positive(XI _v) : v_(std::move(_v)) {}

  explicit Positive(XO _v) : v_(std::move(_v)) {}

  explicit Positive(XH _v) : v_(_v) {}

  static Positive xi(Positive a0) {
    return Positive(XI{std::make_shared<Positive>(std::move(a0))});
  }

  static Positive xo(Positive a0) {
    return Positive(XO{std::make_shared<Positive>(std::move(a0))});
  }

  static Positive xh() { return Positive(XH{}); }

  // MANIPULATORS
  ~Positive() {
    crane::small_vector<std::shared_ptr<Positive>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<XI>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
        }
      }
      if (auto *_alt = std::get_if<XO>(&_v)) {
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

  Positive(const Positive &) = default;
  Positive &operator=(const Positive &) = default;
  Positive(Positive &&) noexcept = default;
  Positive &operator=(Positive &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

/// A local fixpoint of two arguments that is not lifted to a helper, because
/// its return type is recovered from its body.  Every other de-lifted
/// fixpoint in the suite is unary, and a unary one cannot show whether the
/// self-call passes all of its arguments: _self_go(_self_go, p)(x) and
/// _self_go(_self_go, p, x) differ only from arity two up.
///
/// This does not reproduce the curried spine -- the optimiser uncurries this
/// body before translation sees it, whichever way the recursion is written.
/// It covers the arity-two de-lift path, which nothing else did.
struct DeliftedBinaryFixpoint {
  static bool same(Positive a, Positive b);
};

#endif // INCLUDED_DELIFTED_BINARY_FIXPOINT
