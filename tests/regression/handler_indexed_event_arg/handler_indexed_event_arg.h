#ifndef INCLUDED_HANDLER_INDEXED_EVENT_ARG
#define INCLUDED_HANDLER_INDEXED_EVENT_ARG

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <crane_itree.h>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
template <typename T> struct MemM;
template <typename I>
concept Params = requires {
  { I::width() } -> std::convertible_to<Nat>;
};

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
    std::optional<Nat> _root{};
    std::shared_ptr<Nat> *_write = nullptr;
    const Nat *_loop_self = this;
    Nat _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        auto _value = std::move(_loop_m);
        (_write ? *(*_write = std::make_shared<Nat>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0] = std::get<typename Nat::S>(_sv.v());
        auto _cell = typename Nat::S(nullptr);
        Nat &_node =
            (_write ? *(*_write = std::make_shared<Nat>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename Nat::S>(_node.v_mut()).a0;
        _loop_self = crane_raw(a0);
        continue;
      }
    }
    return std::move(*_root);
  }
};

struct Monads {
  template <typename s, template <typename> class m, typename a>
  using stateT = crane::fn<m<std::pair<s, a>>(s)>;
};

using st = Nat;

template <typename T> struct MemM {
  // DATA
  T a0;

  // ACCESSORS
  MemM<T> clone() const { return {a0}; }

  template <typename CraneU> operator MemM<CraneU>() const {
    return {[&]() -> CraneU {
      if constexpr (crane_convertible<CraneU, const T &>) {
        return crane_convert<CraneU>(a0);
      } else {
        throw std::logic_error(
            "unreachable: inactive constructor field at this instantiation");
      }
    }()};
  }

  // CREATORS
  static MemM<T> memret(T a0) { return {std::move(a0)}; }
};

template <typename CraneTcArg>
using itree_tc_609e8855cd7ad294 = std::shared_ptr<ITree<CraneTcArg>>;

template <Params _tcI0, typename T1, typename T2>
Monads::template stateT<st, itree_tc_609e8855cd7ad294, T2> base(MemM<T2> m) {
  return [=](const Nat &s) {
    const auto &[a0] = m;
    return itree_ret(std::make_pair(s.add(_tcI0::width()), a0));
  };
}

template <typename T1, typename T2, typename F0>
Monads::template stateT<st, itree_tc_609e8855cd7ad294, T2>
run(F0 &&h, const MemM<T2> &m) {
  return h(m);
}

template <Params _tcI0, typename T1>
Monads::template stateT<st, itree_tc_609e8855cd7ad294, T1>
fused(const MemM<T1> &m) {
  return run<void, T1>(
      []() {
        return
            []<typename T2>(MemM<T2> _x0)
                -> Monads::template stateT<st, itree_tc_609e8855cd7ad294, T2> {
              return base<_tcI0, void>(_x0);
            };
      }(),
      m);
}

struct HandlerIndexedEventArg {
  template <Params _tcI0>
  static std::shared_ptr<ITree<std::pair<st, Nat>>> go(const Nat &n) {
    return fused<_tcI0, Nat>(MemM<Nat>::memret(n))(n);
  }
};

#endif // INCLUDED_HANDLER_INDEXED_EVENT_ARG
