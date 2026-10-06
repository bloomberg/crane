#ifndef INCLUDED_CASE_HANDLER_CONCRETE_RESULT
#define INCLUDED_CASE_HANDLER_CONCRETE_RESULT

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <crane_itree.h>
#include <cstdint>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A, typename B> struct Sum;
enum class AE;
template <typename I>
concept Functor = requires {
  typename I::template F<crane::obj>;
  {
    I::template fmap<crane::obj, crane::obj>(
        std::declval<crane::fn<crane::obj(crane::obj)>>(),
        std::declval<typename I::template F<crane::obj>>())
  } -> std::convertible_to<typename I::template F<crane::obj>>;
};
template <typename I>
concept Monad = requires {
  typename I::template m<crane::obj>;
  {
    I::template ret<crane::obj>(std::declval<crane::obj>())
  } -> std::convertible_to<typename I::template m<crane::obj>>;
  {
    I::bind(std::declval<typename I::template m<crane::obj>>(),
            std::declval<
                crane::fn<typename I::template m<crane::obj>(crane::obj)>>())
  } -> std::convertible_to<typename I::template m<crane::obj>>;
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

struct Functor0 {
  template <Functor _tcI0, typename T2, typename T3, typename F0>
  static typename _tcI0::template F<T3> fmap(F0 &&x,
                                             typename _tcI0::template F<T2> x0);
};

template <typename I>
concept MonadIter = requires {
  typename I::template M<crane::obj>;
  {
    I::template iter<crane::obj, crane::obj>(
        std::declval<crane::fn<
            typename I::template M<Sum<crane::obj, crane::obj>>(crane::obj)>>(),
        std::declval<crane::obj>())
  } -> std::convertible_to<typename I::template M<crane::obj>>;
};

struct Basics {
  template <MonadIter _tcI0, typename T2, typename T3, typename F0>
  static typename _tcI0::template M<T2> iter(F0 &&x, const T3 &x0);
};

struct Interp {
  template <MonadIter _tcI0, Monad _tcI1, Functor _tcI2, typename T1,
            typename T3>
  static typename _tcI0::template M<T3>
  interp(std::type_identity_t<
             crane::fn<typename _tcI0::template M<crane::obj>(T1)>>
             h,
         std::shared_ptr<ITree<T3>> x0_);
};
enum class AE { A0 };

struct CaseHandlerConcreteResult {
  static std::shared_ptr<ITree<uint64_t>> tl();
  static std::shared_ptr<ITree<uint64_t>> tr();

  template <typename T1> static std::shared_ptr<ITree<T1>> hl(AE) {
    return itree_ret(UINT64_C(1));
  }

  template <typename T1> static std::shared_ptr<ITree<T1>> hr(AE) {
    return itree_ret(UINT64_C(2));
  }

  static uint64_t result(uint64_t fuel,
                         const std::shared_ptr<ITree<uint64_t>> &t);
  static inline const uint64_t handled_left =
      result(UINT64_C(10),
             Interp::template interp<
                 MonadIter_itree<crane::obj>, Monad_itree<crane::obj>,
                 Functor_itree<crane::obj>, Sum1<AE, AE, crane::obj>, uint64_t>(
                 itree_case(
                     [](const AE &a0) -> std::shared_ptr<ITree<crane::obj>> {
                       return hl<crane::obj>(crane_convert<AE>(a0));
                     },
                     [](const AE &a0) -> std::shared_ptr<ITree<crane::obj>> {
                       return hr<crane::obj>(crane_convert<AE>(a0));
                     }),
                 tl()));
  static inline const uint64_t handled_right =
      result(UINT64_C(10),
             Interp::template interp<
                 MonadIter_itree<crane::obj>, Monad_itree<crane::obj>,
                 Functor_itree<crane::obj>, Sum1<AE, AE, crane::obj>, uint64_t>(
                 itree_case(
                     [](const AE &a0) -> std::shared_ptr<ITree<crane::obj>> {
                       return hl<crane::obj>(crane_convert<AE>(a0));
                     },
                     [](const AE &a0) -> std::shared_ptr<ITree<crane::obj>> {
                       return hr<crane::obj>(crane_convert<AE>(a0));
                     }),
                 tr()));
};

template <Functor _tcI0, typename T2, typename T3, typename F0>
typename _tcI0::template F<T3>
Functor0::fmap(F0 &&x, typename _tcI0::template F<T2> x0) {
  return _tcI0::template fmap<T2, T3>(x, std::move(x0));
}

template <MonadIter _tcI0, typename T2, typename T3, typename F0>
typename _tcI0::template M<T2> Basics::iter(F0 &&x, const T3 &x0) {
  return _tcI0::template iter<T2, T3>(x, x0);
}

template <MonadIter _tcI0, Monad _tcI1, Functor _tcI2, typename T1, typename T3>
typename _tcI0::template M<T3> Interp::interp(
    std::type_identity_t<crane::fn<typename _tcI0::template M<crane::obj>(T1)>>
        h,
    std::shared_ptr<ITree<T3>> x0_) {
  return _tcI0::template iter<T3, std::shared_ptr<ITree<T3>>>(
      [=, h = std::move(h)](const std::shared_ptr<ITree<T3>> &t) ->
      typename _tcI0::template M<Sum<std::shared_ptr<ITree<T3>>, T3>> {
        auto _cs = t->observe();
        if (std::holds_alternative<typename ITree<T3>::Ret>(_cs)) {
          const auto &_itf = *std::get_if<typename ITree<T3>::Ret>(&_cs);
          auto r = _itf.value;
          return _tcI1::template ret<Sum<std::shared_ptr<ITree<T3>>, T3>>(
              Sum<std::shared_ptr<ITree<T3>>, T3>::inr(r));
        } else if (std::holds_alternative<typename ITree<T3>::Tau>(_cs)) {
          const auto &_itf = *std::get_if<typename ITree<T3>::Tau>(&_cs);
          auto t0 = _itf.next;
          return _tcI1::template ret<Sum<std::shared_ptr<ITree<T3>>, T3>>(
              Sum<std::shared_ptr<ITree<T3>>, T3>::inl(t0));
        } else {
          const auto &_itf = *std::get_if<typename ITree<T3>::Vis>(&_cs);
          auto e = crane_event_as<T1>(_itf.effect);
          auto k = _itf.cont;
          return Functor0::template fmap<_tcI2, crane::obj,
                                         Sum<std::shared_ptr<ITree<T3>>, T3>>(
              [=](const auto &x) {
                return Sum<std::shared_ptr<ITree<T3>>, T3>::inl(k(x));
              },
              h(e));
        }
      },
      std::move(x0_));
}

#endif // INCLUDED_CASE_HANDLER_CONCRETE_RESULT
