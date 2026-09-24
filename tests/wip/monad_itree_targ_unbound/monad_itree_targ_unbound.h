#ifndef INCLUDED_MONAD_ITREE_TARG_UNBOUND
#define INCLUDED_MONAD_ITREE_TARG_UNBOUND

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <crane_itree.h>
#include <functional>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

struct Empty_set;
struct Nat;
struct FailE;
enum class Ev;

struct Empty_set {
  Empty_set() = delete;
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

  bool eqb(const Nat &m) const {
    const Nat *_loop_self = this;
    const Nat *_loop_m = &m;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        if (std::holds_alternative<typename Nat::O>(_loop_m->v())) {
          return true;
        } else {
          return false;
        }
      } else {
        const auto &[a0] = std::get<typename Nat::S>(_sv.v());
        if (std::holds_alternative<typename Nat::O>(_loop_m->v())) {
          return false;
        } else {
          const auto &[a00] = std::get<typename Nat::S>(_loop_m->v());
          _loop_self = crane_raw(a0);
          _loop_m = crane_raw(a00);
        }
      }
    }
  }

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

template <typename I>
concept Monad = requires {
  typename I::template m<std::any>;
  {
    I::template ret<std::any>(std::declval<std::any>())
  } -> std::convertible_to<typename I::template m<std::any>>;
  {
    I::template bind<std::any, std::any>(
        std::declval<typename I::template m<std::any>>(),
        std::declval<
            std::function<typename I::template m<std::any>(std::any)>>())
  } -> std::convertible_to<typename I::template m<std::any>>;
};

struct Monads {
  template <typename s, template <typename> class m, typename a>
  using stateT = std::function<m<std::pair<s, a>>(s)>;

  template <Monad _tcI0, typename T1> struct Monad_stateT {
    template <typename _A0> using m = typename _tcI0::template m<_A0>;

    template <typename _A0>
    static std::function<typename _tcI0::template m<std::pair<T1, _A0>>(T1)>
    ret(_A0 a) {
      return [=](T1 s) mutable { return itree_ret(std::make_pair(s, a)); };
    }

    template <typename _A0, typename _A1>
    static std::function<typename _tcI0::template m<std::pair<T1, _A1>>(T1)>
    bind(std::function<typename _tcI0::template m<std::pair<T1, _A0>>(T1)> t,
         std::function<std::function<
             typename _tcI0::template m<std::pair<T1, _A1>>(T1)>(_A0)>
             k) {
      return [=](const T1 &s) mutable {
        return itree_bind(t(s), [=](const auto &sa) mutable {
          return k(sa.second)(sa.first);
        });
      };
    }
  };
};

struct FailE {
  // DATA
  std::monostate a0;

  // ACCESSORS
  FailE clone() const { return {a0}; }

  // CREATORS
  static FailE Throw_(std::monostate a0) { return {a0}; }
};
enum class Ev { EV0 };
template <typename I>
concept Params = requires {
  { I::width() } -> std::convertible_to<Nat>;
};
using env = Nat;
template <typename _CraneTcArg>
using itree_tc_296b3b7af4bd1a71 = std::shared_ptr<ITree<_CraneTcArg>>;

template <Params _tcI0, typename T1 = void>
Monads::template stateT<env, itree_tc_296b3b7af4bd1a71, Nat> step(Nat n) {
  return [=](Nat s) mutable {
    return itree_ret(std::make_pair(s, n.add(_tcI0::width())));
  };
}

template <typename T1 = void, typename T2>
Monads::template stateT<env, itree_tc_296b3b7af4bd1a71, T2> handle(Ev) {
  return [](Nat s) {
    if (s.eqb(Nat::o())) {
      return itree_vis(FailE::Throw_(std::monostate{}), [](const auto &) {
        throw std::logic_error("absurd case");
      });
    } else {
      return itree_ret(std::make_pair(s, s));
    }
  };
}

template <Params _tcI0, typename T1 = void, typename T2>
Monads::template stateT<env, itree_tc_296b3b7af4bd1a71, T2> twice(Ev e) {
  return Monads::template Monad_stateT<Monad_itree<T1>, env>::template bind<
      T2, T2>(handle<T1, T2>(e), [](const auto &res) {
    return Monads::template Monad_stateT<Monad_itree<T1>, env>::template bind<
        Nat, T2>(step<_tcI0, T1>(Nat::s(Nat::o())), [=](const Nat &) mutable {
      return Monads::template Monad_stateT<Monad_itree<T1>,
                                           env>::template ret<T2>(res);
    });
  });
}

struct Qf {
  template <Params _tcI0>
  static std::shared_ptr<ITree<std::pair<Nat, env>>> use(const Nat &n) {
    return twice<_tcI0, FailE, Nat>(Ev::EV0)(n);
  }
};

#endif // INCLUDED_MONAD_ITREE_TARG_UNBOUND
