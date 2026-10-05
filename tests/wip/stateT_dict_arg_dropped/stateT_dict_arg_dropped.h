#ifndef INCLUDED_STATET_DICT_ARG_DROPPED
#define INCLUDED_STATET_DICT_ARG_DROPPED

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
template <typename S, typename m, typename t> struct stateT;
struct FailE;
template <typename I>
concept Monad = requires {
  typename I::template m<crane::obj>;
  {
    I::template ret<crane::obj>(std::declval<crane::obj>())
  } -> std::convertible_to<typename I::template m<crane::obj>>;
  {
    I::template bind<crane::obj, crane::obj>(
        std::declval<typename I::template m<crane::obj>>(),
        std::declval<
            crane::fn<typename I::template m<crane::obj>(crane::obj)>>())
  } -> std::convertible_to<typename I::template m<crane::obj>>;
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
};

template <typename S, typename m, typename t> struct stateT {
  crane::fn<m(S)> runStateT;

  // ACCESSORS
  template <typename CraneU0, typename CraneU1, typename CraneU2>
  operator stateT<CraneU0, CraneU1, CraneU2>() const {
    return {crane_convert<crane::fn<CraneU1(CraneU0)>>(runStateT)};
  }
};

template <Monad _tcI0, typename T1> struct Monad_stateT {
  template <typename CraneA0>
  using m = stateT<T1, typename _tcI0::template m<CraneA0>, CraneA0>;

  template <typename CraneA0>
  static stateT<T1, typename _tcI0::template m<CraneA0>, CraneA0>
  ret(CraneA0 x) {
    return stateT<T1, typename _tcI0::template m<CraneA0>, CraneA0>{
        [=](const T1 &s) { return itree_ret(std::make_pair(x, s)); }};
  }

  template <typename CraneA0, typename CraneA1>
  static stateT<T1, typename _tcI0::template m<CraneA1>, CraneA1>
  bind(stateT<T1, typename _tcI0::template m<CraneA0>, CraneA0> c1,
       crane::fn<
           stateT<T1, typename _tcI0::template m<CraneA1>, CraneA1>(CraneA0)>
           c2) {
    return stateT<T1, typename _tcI0::template m<CraneA1>, CraneA1>{
        [=](const T1 &s) {
          return itree_bind(
              crane_container_cast<
                  typename _tcI0::template m<std::pair<CraneA0, T1>>>(
                  c1.runStateT(s)),
              [=](const std::pair<CraneA0, T1> &vs) {
                const auto &[v, s0] = vs;
                return crane_container_cast<
                    typename _tcI0::template m<std::pair<CraneA1, T1>>>(
                    c2(v).runStateT(s0));
              });
        }};
  }
};

struct FailE {
  // DATA
  std::monostate a0;

  // ACCESSORS
  FailE clone() const { return {a0}; }

  // CREATORS
  static FailE Throw_(std::monostate a0) { return {a0}; }
};

using env = Nat;

template <typename T1 = void>
stateT<env, std::shared_ptr<ITree<crane::obj>>, Nat> step(Nat n) {
  return stateT<Nat, std::shared_ptr<ITree<crane::obj>>, Nat>{
      [=](const Nat &s) { return itree_ret(std::make_pair(n, s)); }};
}

template <typename T1 = void>
stateT<env, std::shared_ptr<ITree<crane::obj>>, Nat> twice(Nat n) {
  return Monad_stateT<Monad_itree<crane::obj>, env>::template bind<Nat, Nat>(
      step<crane::obj>(std::move(n)), [](Nat a) {
        return Monad_stateT<Monad_itree<crane::obj>, env>::template bind<
            Nat, Nat>(step<crane::obj>(a), [](const Nat &b) {
          return Monad_stateT<Monad_itree<crane::obj>, env>::template ret<Nat>(
              b);
        });
      });
}

struct StateTDictArgDropped {
  static std::shared_ptr<ITree<std::pair<Nat, env>>> use(Nat n);
};

#endif // INCLUDED_STATET_DICT_ARG_DROPPED
