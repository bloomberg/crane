#ifndef INCLUDED_HANDLER_LAMBDA_TARG_UNDECLARED
#define INCLUDED_HANDLER_LAMBDA_TARG_UNDECLARED

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <crane_itree.h>
#include <memory>
#include <utility>
#include <variant>

struct Nat;
enum class LocalE;
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
  using stateT = crane::fn<m<std::pair<s, a>>(s)>;
};
enum class LocalE { LGET };
using lenv = Nat;
using Big = std::pair<Nat, Nat>;
template <typename CraneTcArg>
using itree_tc_609e8855cd7ad294 = std::shared_ptr<ITree<CraneTcArg>>;

template <Params _tcI0, typename T1, typename T2>
Monads::template stateT<lenv, itree_tc_609e8855cd7ad294, T2>
handle_local_debug(LocalE) {
  return [=](const Nat &s) {
    return itree_ret(std::make_pair(s, s.add(_tcI0::width())));
  };
}

template <typename T1, typename T2, typename F0>
Monads::template stateT<lenv, itree_tc_609e8855cd7ad294, T2>
handle_local_stack(F0 &&h, LocalE e) {
  return h(e);
}

template <typename T1, typename T2>
Monads::template stateT<Big, itree_tc_609e8855cd7ad294, T2>
on_ls(std::type_identity_t<
      Monads::template stateT<lenv, itree_tc_609e8855cd7ad294, T2>>
          c) {
  return [=](const std::pair<Nat, Nat> &b) {
    std::pair<lenv, T2> sa = c(b.first);
    return itree_ret(
        std::make_pair(std::make_pair(sa.first, b.second), sa.second));
  };
}

template <Params _tcI0, typename T1>
Monads::template stateT<Big, itree_tc_609e8855cd7ad294, T1>
fused_local(LocalE e) {
  return on_ls<LocalE, T1>(handle_local_stack<LocalE, T1>(
      []() {
        return [](LocalE _x0) -> Monads::template stateT<
                                  lenv, itree_tc_609e8855cd7ad294, crane::obj> {
          return handle_local_debug<_tcI0, LocalE, crane::obj>(_x0);
        };
      }(),
      e));
}

template <Params _tcI0>
std::shared_ptr<ITree<std::pair<Big, Nat>>> use(const Nat &n) {
  return fused_local<_tcI0, Nat>(LocalE::LGET)(std::make_pair(n, n));
}

struct HandlerLambdaTargUndeclared {
  template <Params _tcI0>
  static std::shared_ptr<ITree<std::pair<Big, Nat>>> go(const Nat &x1_) {
    return use<_tcI0>(x1_);
  }
};

#endif // INCLUDED_HANDLER_LAMBDA_TARG_UNDECLARED
