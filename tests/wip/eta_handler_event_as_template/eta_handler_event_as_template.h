#ifndef INCLUDED_ETA_HANDLER_EVENT_AS_TEMPLATE
#define INCLUDED_ETA_HANDLER_EVENT_AS_TEMPLATE

#include "fn.h"
#include "obj.h"
#include <atomic>
#include <crane_itree.h>
#include <memory>
#include <utility>
#include <variant>

struct Nat;
enum class AE;
struct FailE;

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

struct Monads {
  template <typename s, template <typename> class m, typename a>
  using stateT = crane::fn<m<std::pair<s, a>>(s)>;
};
enum class AE { A0 };

struct FailE {
  // DATA
  std::monostate a0;

  // ACCESSORS
  FailE clone() const { return {a0}; }

  // CREATORS
  static FailE Throw_(std::monostate a0) { return {a0}; }
};

using st = Nat;
template <typename CraneTcArg>
using itree_tc_609e8855cd7ad294 = std::shared_ptr<ITree<CraneTcArg>>;

struct M {
  template <typename T1, typename T2>
  static Monads::template stateT<st, itree_tc_609e8855cd7ad294, T2> base(AE) {
    return [](const Nat &s) { return itree_ret(std::make_pair(s, s)); };
  }

  template <typename T1, typename T2>
  static Monads::template stateT<st, itree_tc_609e8855cd7ad294, T2>
  run(std::type_identity_t<crane::fn<Monads::template stateT<
          st, itree_tc_609e8855cd7ad294, crane::obj>(AE)>>
          h,
      AE e) {
    return [=](const Nat &s) { return crane::apply2(h, e, s); };
  }

  template <typename T1, typename T2>
  static Monads::template stateT<st, itree_tc_609e8855cd7ad294, T2>
  fused(AE e) {
    return run<T1, T2>(
        [](const AE &a0) -> decltype(auto) {
          return base<T1>(std::forward<decltype(a0)>(a0));
        },
        e);
  }

  static std::shared_ptr<ITree<std::pair<Nat, Nat>>> use(const Nat &n);
};

#endif // INCLUDED_ETA_HANDLER_EVENT_AS_TEMPLATE
