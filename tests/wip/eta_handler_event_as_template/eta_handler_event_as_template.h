#ifndef INCLUDED_ETA_HANDLER_EVENT_AS_TEMPLATE
#define INCLUDED_ETA_HANDLER_EVENT_AS_TEMPLATE

#include "small_vector.h"
#include <atomic>
#include <crane_itree.h>
#include <functional>
#include <memory>
#include <utility>
#include <variant>

struct Nat;
enum class AE;
struct FailE;
template <typename _CraneTcArg>
using itree_tc_296b3b7af4bd1a71 = std::shared_ptr<ITree<_CraneTcArg>>;

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

struct Monads {
  template <typename s, template <typename> class m, typename a>
  using stateT = std::function<m<std::pair<s, a>>(s)>;
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

struct M {
  template <typename T1 = void, typename T2>
  static Monads::template stateT<st, itree_tc_296b3b7af4bd1a71, T2> base(AE) {
    return [](Nat s) { return itree_ret(std::make_pair(s, s)); };
  }

  template <typename T1 = void, typename T2, typename F0>
  static Monads::template stateT<st, itree_tc_296b3b7af4bd1a71, T2> run(F0 &&h,
                                                                        AE e) {
    return [=](const Nat &s) mutable { return h(e)(s); };
  }

  template <typename T1 = void, typename T2>
  static Monads::template stateT<st, itree_tc_296b3b7af4bd1a71, T2>
  fused(AE e) {
    return run<T1, T2>(
        []<typename _T2>(const AE<_T2> &a0) -> decltype(auto) {
          return base<_T2, std::invoke_result_t<decltype(a0) &, _T2 &>>(a0);
        },
        e);
  }

  static std::shared_ptr<ITree<std::pair<Nat, Nat>>> use(const Nat &n);
};

#endif // INCLUDED_ETA_HANDLER_EVENT_AS_TEMPLATE
