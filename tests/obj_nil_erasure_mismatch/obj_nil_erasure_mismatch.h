#ifndef INCLUDED_OBJ_NIL_ERASURE_MISMATCH
#define INCLUDED_OBJ_NIL_ERASURE_MISMATCH

#include "small_vector.h"
#include <any>
#include <atomic>
#include <deque>
#include <functional>
#include <memory>
#include <utility>
#include <variant>

enum class Unit { TT };

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

template <typename A, typename B> struct Prod {
  // DATA
  A a0;
  B a1;

  // ACCESSORS
  Prod<A, B> clone() const { return {a0, a1}; }

  // CREATORS
  static Prod<A, B> pair(A a0, B a1) { return {std::move(a0), std::move(a1)}; }
};

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

  // CREATORS
  static SigT<A, P> existt(A x, P a1) { return {std::move(x), std::move(a1)}; }
};
enum class Sym { TOPSYM, PAIRSYM, PAIRSSYM };
using semty = std::any;
const std::deque<SigT<Sym, std::function<semty(Unit)>>> entries =
    [](auto _a0, auto _a1) {
      _a1.push_front(_a0);
      return _a1;
    }(SigT<Sym, std::function<std::any(Unit)>>::existt(
          Sym::PAIRSYM,
          [](Unit) {
            return Prod<std::any, std::any>::pair(
                Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))),
                Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))))));
          }),
      [](auto _a0, auto _a1) {
        _a1.push_front(_a0);
        return _a1;
      }(SigT<Sym, std::function<std::any(Unit)>>::existt(
            Sym::PAIRSSYM,
            [](Unit) {
              return [](auto _a0, auto _a1) {
                _a1.push_front(_a0);
                return _a1;
              }(std::any(Prod<std::any, std::any>::pair(
                         Nat::s(Nat::o()), Nat::s(Nat::s(Nat::o())))),
                     [](auto _a0, auto _a1) {
                       _a1.push_front(_a0);
                       return _a1;
                     }(std::any(Prod<std::any, std::any>::pair(
                           Nat::s(Nat::s(Nat::s(Nat::o()))),
                           Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))))),
                       std::deque<std::any>{}));
            }),
        [](auto _a0, auto _a1) {
          _a1.push_front(_a0);
          return _a1;
        }(SigT<Sym, std::function<std::any(Unit)>>::existt(
              Sym::PAIRSSYM, [](Unit) { return std::deque<std::any>{}; }),
          [](auto _a0, auto _a1) {
            _a1.push_front(_a0);
            return _a1;
          }(SigT<Sym, std::function<std::any(Unit)>>::existt(
                Sym::TOPSYM,
                [](Unit) {
                  return [](auto _a0, auto _a1) {
                    _a1.push_front(_a0);
                    return _a1;
                  }(std::any(Prod<std::any, std::any>::pair(
                             Nat::s(Nat::s(Nat::s(
                                 Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))))),
                             Nat::s(Nat::s(Nat::s(Nat::s(
                                 Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))))))))),
                         std::deque<std::any>{});
                }),
            [](auto _a0, auto _a1) {
              _a1.push_front(_a0);
              return _a1;
            }(SigT<Sym, std::function<std::any(Unit)>>::existt(
                  Sym::TOPSYM, [](Unit) { return std::deque<std::any>{}; }),
              std::deque<SigT<Sym, std::function<std::any(Unit)>>>{})))));
std::deque<Prod<Nat, Nat>> top_cons_action(Unit _x);
std::deque<Prod<Nat, Nat>> top_nil_action(Unit _x);

#endif // INCLUDED_OBJ_NIL_ERASURE_MISMATCH
