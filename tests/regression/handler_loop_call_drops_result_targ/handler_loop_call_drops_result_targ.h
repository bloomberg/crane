#ifndef INCLUDED_HANDLER_LOOP_CALL_DROPS_RESULT_TARG
#define INCLUDED_HANDLER_LOOP_CALL_DROPS_RESULT_TARG

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <crane_itree.h>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
template <typename A, typename B> struct Sum;
struct natParams;
using ptr = crane::obj;
template <typename
I>concept Params = requires {
    typename I::ptr;
  } && (requires {
    { I::nullp() } -> std::convertible_to<typename I::ptr>;
  } || requires {
    { I::nullp } -> std::convertible_to<typename I::ptr>;
  });

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

template <typename A, typename B> struct Sum {
  // TYPES
  struct Inl {
    A a0;
  };

  struct Inr {
    B a0;
  };

  using variant_t = std::variant<Inl, Inr>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Sum() {}

  explicit Sum(Inl _v) : v_(std::move(_v)) {}

  explicit Sum(Inr _v) : v_(std::move(_v)) {}

  template <typename CraneU0, typename CraneU1>
  Sum(const Sum<CraneU0, CraneU1> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename Sum<CraneU0, CraneU1>::Inl>(
                  _other.v())) {
            const auto &[a0] =
                std::get<typename Sum<CraneU0, CraneU1>::Inl>(_other.v());
            return Inl{[&]() -> A {
              if constexpr (crane_convertible<A, const CraneU0 &>) {
                return crane_convert<A>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            const auto &[a0] =
                std::get<typename Sum<CraneU0, CraneU1>::Inr>(_other.v());
            return Inr{[&]() -> B {
              if constexpr (crane_convertible<B, const CraneU1 &>) {
                return crane_convert<B>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          }
        }()) {}

  static Sum<A, B> inl(A a0) { return Sum<A, B>(Inl{std::move(a0)}); }

  static Sum<A, B> inr(B a0) { return Sum<A, B>(Inr{std::move(a0)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Denot {
  template <typename ptr> struct dvalue {
    // TYPES
    struct DP {
      ptr a0;
    };

    struct DU {};

    using variant_t = std::variant<DP, DU>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    dvalue() {}

    explicit dvalue(DP _v) : v_(std::move(_v)) {}

    explicit dvalue(DU _v) : v_(_v) {}

    template <typename CraneU>
    dvalue(const dvalue<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename dvalue<CraneU>::DP>(
                    _other.v())) {
              const auto &[a0] =
                  std::get<typename dvalue<CraneU>::DP>(_other.v());
              return DP{[&]() -> ptr {
                if constexpr (crane_convertible<ptr, const CraneU &>) {
                  return crane_convert<ptr>(a0);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }()};
            } else {
              return DU{};
            }
          }()) {}

    static dvalue<ptr> dp(ptr a0) { return dvalue<ptr>(DP{std::move(a0)}); }

    static dvalue<ptr> du() { return dvalue<ptr>(DU{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename ptr> using exc = dvalue<ptr>;

  template <typename ptr> struct FailE {
    // DATA
    dvalue<ptr> a0;

    // ACCESSORS
    FailE<ptr> clone() const { return {a0}; }

    template <typename CraneU> operator FailE<CraneU>() const { return {a0}; }

    // CREATORS
    static FailE<ptr> fail(dvalue<ptr> a0) { return {std::move(a0)}; }
  };

  struct OtherE {
    // DATA
    Nat a0;

    // ACCESSORS
    OtherE clone() const { return {a0}; }

    // CREATORS
    static OtherE other(Nat a0) { return {std::move(a0)}; }
  };

  template <typename ptr, typename x = void>
  using CFGEtop = Sum1<OtherE, FailE<ptr>, x>;
  template <typename ptr, typename r> using CFGtop = std::shared_ptr<ITree<r>>;

  template <Params _tcI0, typename T1>
  static Sum<Nat, T1> handle_bot(CFGEtop<typename _tcI0::ptr, T1> e) {
    if (std::holds_alternative<
            typename Sum1<OtherE, FailE<typename _tcI0::ptr>, T1>::Inl1>(
            e.v())) {
      const auto &[a0] =
          std::get<typename Sum1<OtherE, FailE<typename _tcI0::ptr>, T1>::Inl1>(
              e.v());
      const auto &[a00] = a0;
      return Sum<Nat, T1>::inr(a00);
    } else {
      return Sum<Nat, T1>::inl(Nat::o());
    }
  }

  template <Params _tcI0, typename T1>
  static CFGtop<typename _tcI0::ptr, Sum<exc<typename _tcI0::ptr>, T1>>
  run_exc(CFGtop<typename _tcI0::ptr, T1> t) {
    return itree_iter(
        [](const std::shared_ptr<ITree<T1>> &u)
            -> std::shared_ptr<
                ITree<Sum<std::shared_ptr<ITree<T1>>,
                          Sum<dvalue<typename _tcI0::ptr>, T1>>>> {
          auto _cs = u->observe();
          if (std::holds_alternative<typename ITree<T1>::Ret>(_cs)) {
            const auto &_itf = *std::get_if<typename ITree<T1>::Ret>(&_cs);
            auto a = _itf.value;
            return itree_ret(
                Sum<std::shared_ptr<ITree<T1>>,
                    Sum<dvalue<typename _tcI0::ptr>, T1>>::
                    inr(Sum<dvalue<typename _tcI0::ptr>, T1>::inr(a)));
          } else if (std::holds_alternative<typename ITree<T1>::Tau>(_cs)) {
            const auto &_itf = *std::get_if<typename ITree<T1>::Tau>(&_cs);
            auto u_ = _itf.next;
            return itree_ret(
                Sum<std::shared_ptr<ITree<T1>>,
                    Sum<dvalue<typename _tcI0::ptr>, T1>>::inl(u_));
          } else {
            const auto &_itf = *std::get_if<typename ITree<T1>::Vis>(&_cs);
            auto e = crane_event_as<
                Sum1<OtherE, FailE<typename _tcI0::ptr>, crane::obj>>(
                _itf.effect);
            auto k = _itf.cont;
            auto &&_sv = handle_bot<_tcI0, crane::obj>(e);
            if (std::holds_alternative<typename Sum<Nat, crane::obj>::Inl>(
                    _sv.v())) {
              return itree_ret(
                  Sum<std::shared_ptr<ITree<T1>>,
                      Sum<dvalue<typename _tcI0::ptr>, T1>>::
                      inr(Sum<dvalue<typename _tcI0::ptr>, T1>::inl(
                          dvalue<typename _tcI0::ptr>::du())));
            } else {
              const auto &[a0] =
                  std::get<typename Sum<Nat, crane::obj>::Inr>(_sv.v());
              return itree_ret(Sum<std::shared_ptr<ITree<T1>>,
                                   Sum<dvalue<typename _tcI0::ptr>,
                                       T1>>::inl(crane_call_erased(k, a0)));
            }
          }
        },
        t);
  }
};

struct natParams {
  using ptr = Nat;

  static Nat nullp() { return Nat::o(); }
};

static_assert(Params<natParams>);

struct HandlerLoopCallDropsResultTarg {
  static std::shared_ptr<
      ITree<Sum<Denot::template exc<typename natParams::ptr>, Nat>>>
  run();
};

#endif // INCLUDED_HANDLER_LOOP_CALL_DROPS_RESULT_TARG
