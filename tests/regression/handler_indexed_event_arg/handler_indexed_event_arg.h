#ifndef INCLUDED_HANDLER_INDEXED_EVENT_ARG
#define INCLUDED_HANDLER_INDEXED_EVENT_ARG

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <concepts>
#include <crane_itree.h>
#include <functional>
#include <memory>
#include <utility>
#include <variant>

struct Nat;
template <typename T> struct MemM;
template <typename _CraneTcArg>
using itree_tc = std::shared_ptr<ITree<_CraneTcArg>>;

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

struct Monads {
  template <typename s, template <typename> class m, typename a>
  using stateT = std::function<m<std::pair<s, a>>(s)>;
};

using st = Nat;

template <typename T> struct MemM {
  // DATA
  T a0;

  // ACCESSORS
  MemM<T> clone() const { return {a0}; }

  // CREATORS
  static MemM<T> memret(T a0) { return {std::move(a0)}; }
};

template <typename I>
concept Params = requires {
  { I::width() } -> std::convertible_to<Nat>;
};

template <Params _tcI0, typename T1 = void, typename T2>
Monads::template stateT<st, itree_tc, T2> base(MemM<T2> m) {
  return [=](const Nat &s) mutable {
    const auto &[a0] = m;
    return itree_ret(std::make_pair(s.add(_tcI0::width()), a0));
  };
}

template <typename T1 = void, typename T2, typename F0>
Monads::template stateT<st, itree_tc, T2> run(F0 &&h, const MemM<T2> &m) {
  return h(m);
}

template <Params _tcI0, typename T1>
Monads::template stateT<st, itree_tc, T1> fused(const MemM<T1> &m) {
  return run(
      []() {
        return []<typename T2>(
                   MemM<T2> _x0) -> Monads::template stateT<st, itree_tc, T2> {
          return base<_tcI0>(_x0);
        };
      }(),
      m);
}

struct HandlerIndexedEventArg {
  template <Params _tcI0>
  static std::shared_ptr<ITree<std::pair<st, Nat>>> go(Nat n) {
    return fused<_tcI0, Nat>(MemM<Nat>::memret(n))(n);
  }
};

#endif // INCLUDED_HANDLER_INDEXED_EVENT_ARG
