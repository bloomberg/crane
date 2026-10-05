#ifndef INCLUDED_DOUBLE_OPPOSITE_WITNESSES
#define INCLUDED_DOUBLE_OPPOSITE_WITNESSES

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <concepts>
#include <cstdint>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A, typename P> struct SigT;

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

  template <typename CraneU0, typename CraneU1>
  operator SigT<CraneU0, CraneU1>() const {
    return {[&]() -> CraneU0 {
              if constexpr (crane_convertible<CraneU0, const A &>) {
                return crane_convert<CraneU0>(x);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }(),
            [&]() -> CraneU1 {
              if constexpr (crane_convertible<CraneU1, const P &>) {
                return crane_convert<CraneU1>(a1);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
  }

  // CREATORS
  static SigT<A, P> existt(A x, P a1) { return {std::move(x), std::move(a1)}; }

  A projT1() const {
    const auto &[x0, a1] = *this;
    return x0;
  }

  P projT2() const {
    const auto &[x0, a1] = *this;
    return a1;
  }
};

template <typename I>
concept PreCategory = requires {
  typename I::Obj;
  {
    I::identity(std::declval<typename I::Obj>())
  } -> std::convertible_to<crane::obj>;
  {
    I::compose(std::declval<typename I::Obj>(), std::declval<typename I::Obj>(),
               std::declval<typename I::Obj>(), std::declval<crane::obj>(),
               std::declval<crane::obj>())
  } -> std::convertible_to<crane::obj>;
};
template <typename I, typename Obj>
concept PreStableCategory = requires {
  typename I::base_category;
  { I::zero_object() } -> std::convertible_to<typename I::base_category::Obj>;
  {
    I::suspension(std::declval<typename I::base_category::Obj>())
  } -> std::convertible_to<typename I::base_category::Obj>;
};

struct DoubleOppositeWitnessesCase {
  template <typename A> struct Path {
    // ACCESSORS
    Path<A> clone() const { return {}; }

    // CREATORS
    static Path<A> path_refl() { return {}; }
  };

  template <typename T1, typename T2>
  static T2 Path_rect(const T1 &, T2 f, const T1 &, const Path<T1> &) {
    return f;
  }

  template <typename T1, typename T2>
  static T2 Path_rec(const T1 &_x, T2 f, const T1 &_x0, const Path<T1> &_x1) {
    return Path_rect<T1, T2>(_x, std::move(f), _x0, _x1);
  }

  template <typename T1>
  static uint64_t path_code(const T1 &, const T1 &, const Path<T1> &) {
    return UINT64_C(1);
  }

  using Obj = crane::obj;
  using Hom = crane::obj;

  template <PreCategory _tcI0> struct opposite_category {
    using Obj = typename _tcI0::Obj;

    static crane::obj identity(typename _tcI0::Obj x) {
      return crane_erase_fn(_tcI0::identity(std::move(x)));
    }

    static crane::obj compose(typename _tcI0::Obj x, typename _tcI0::Obj y,
                              typename _tcI0::Obj z, crane::obj f,
                              crane::obj g) {
      return crane_erase_fn(
          _tcI0::compose(std::move(z), std::move(y), std::move(x), g, f));
    }
  };

  template <typename Obj> struct Functor {
    crane::fn<Obj(Obj)> object_of;
    crane::fn<Hom(Obj, Obj, Hom)> morphism_of;
  };

  template <PreCategory _tcI0, PreCategory _tcI1, PreCategory _tcI2>
  static Functor<typename _tcI0::Obj>
  compose_functor(Functor<typename _tcI0::Obj> f,
                  Functor<typename _tcI0::Obj> g) {
    return Functor<typename _tcI0::Obj>{
        [=](const typename _tcI0::Obj &x) {
          return f.object_of(g.object_of(x));
        },
        crane_erase_fn<Hom>([=](const typename _tcI0::Obj &x,
                                const typename _tcI0::Obj &y, const auto &f0) {
          return f.morphism_of(g.object_of(x), g.object_of(y),
                               crane_erase_fn(g.morphism_of(x, y, f0)));
        })};
  }

  template <typename _tcI0>
    requires PreStableCategory<_tcI0, typename _tcI0::base_category::Obj>
  struct opposite_prestable_category {
    using base_category = opposite_category<typename _tcI0::base_category>;
    using Obj = typename base_category::Obj;

    static typename _tcI0::base_category::Obj zero_object() {
      return _tcI0::zero_object();
    }

    static typename _tcI0::base_category::Obj
    suspension(typename _tcI0::base_category::Obj x) {
      return _tcI0::suspension(std::move(x));
    }
  };

  struct nat_category {
    using Obj = uint64_t;

    static crane::obj identity(uint64_t x) { return x; }

    static crane::obj compose(uint64_t, uint64_t, uint64_t, crane::obj f,
                              crane::obj g) {
      return (crane::any_cast<uint64_t>(f) + crane::any_cast<uint64_t>(g));
    }
  };

  static_assert(PreCategory<nat_category>);

  struct toy_prestable {
    using base_category = nat_category;
    using Obj = typename base_category::Obj;

    static Obj zero_object() { return UINT64_C(0); }

    static Obj suspension(uint64_t x) { return (x + 1); }
  };

  static_assert(PreStableCategory<toy_prestable, Obj>);

  template <PreCategory _tcI0>
  static Functor<typename _tcI0::Obj> into_double_opposite_functor() {
    return Functor<typename _tcI0::Obj>{
        [](typename _tcI0::Obj x) { return x; },
        crane_erase_fn<Hom>([](const typename _tcI0::Obj &,
                               const typename _tcI0::Obj &,
                               const auto &f) { return f; })};
  }

  template <PreCategory _tcI0>
  static Functor<typename _tcI0::Obj> out_of_double_opposite_functor() {
    return into_double_opposite_functor<_tcI0>();
  }

  template <typename _tcI0>
    requires PreStableCategory<_tcI0, typename _tcI0::base_category::Obj>
  static SigT<Functor<typename _tcI0::base_category::Obj>,
              SigT<Functor<typename _tcI0::base_category::Obj>,
                   std::pair<crane::fn<Path<typename _tcI0::base_category::Obj>(
                                 typename _tcI0::base_category::Obj)>,
                             crane::fn<Path<typename _tcI0::base_category::Obj>(
                                 typename _tcI0::base_category::Obj)>>>>
  duality_involution() {
    return SigT<
        Functor<typename _tcI0::base_category::Obj>,
        SigT<Functor<typename _tcI0::base_category::Obj>,
             std::pair<crane::fn<Path<typename _tcI0::base_category::Obj>(
                           typename _tcI0::base_category::Obj)>,
                       crane::fn<Path<typename _tcI0::base_category::Obj>(
                           typename _tcI0::base_category::Obj)>>>>::
        existt(
            into_double_opposite_functor<typename _tcI0::base_category>(),
            SigT<Functor<typename _tcI0::base_category::Obj>,
                 std::pair<crane::fn<Path<typename _tcI0::base_category::Obj>(
                               typename _tcI0::base_category::Obj)>,
                           crane::fn<Path<typename _tcI0::base_category::Obj>(
                               typename _tcI0::base_category::Obj)>>>::
                existt(
                    out_of_double_opposite_functor<
                        typename _tcI0::base_category>(),
                    std::make_pair(
                        [](typename _tcI0::base_category::Obj) {
                          return Path<
                              typename _tcI0::base_category::Obj>::path_refl();
                        },
                        [](typename _tcI0::base_category::Obj) {
                          return Path<
                              typename _tcI0::base_category::Obj>::path_refl();
                        })));
  }

  static inline const SigT<
      Functor<typename toy_prestable::base_category::Obj>,
      SigT<Functor<typename toy_prestable::base_category::Obj>,
           std::pair<crane::fn<Path<uint64_t>(uint64_t)>,
                     crane::fn<Path<uint64_t>(uint64_t)>>>>
      toy_duality_involution = crane::any_cast<
          SigT<Functor<typename toy_prestable::base_category::Obj>,
               SigT<Functor<typename toy_prestable::base_category::Obj>,
                    std::pair<crane::fn<Path<uint64_t>(uint64_t)>,
                              crane::fn<Path<uint64_t>(uint64_t)>>>>>(
          duality_involution<toy_prestable>());
  static inline const Functor<typename toy_prestable::base_category::Obj>
      forward_functor = toy_duality_involution.projT1();
  static inline const SigT<Functor<typename toy_prestable::base_category::Obj>,
                           std::pair<crane::fn<Path<uint64_t>(uint64_t)>,
                                     crane::fn<Path<uint64_t>(uint64_t)>>>
      backward_package = toy_duality_involution.projT2();
  static inline const Functor<typename opposite_prestable_category<
      opposite_prestable_category<toy_prestable>>::base_category::Obj>
      backward_functor = backward_package.projT1();
  static inline const std::pair<crane::fn<Path<uint64_t>(uint64_t)>,
                                crane::fn<Path<uint64_t>(uint64_t)>>
      identity_witnesses = backward_package.projT2();
  static inline const uint64_t forward_object_7 =
      crane::any_cast<uint64_t>(forward_functor.object_of(UINT64_C(7)));
  static inline const uint64_t backward_object_9 =
      crane::any_cast<uint64_t>(backward_functor.object_of(UINT64_C(9)));
  static inline const uint64_t forward_morphism_3 = crane::any_cast<uint64_t>(
      forward_functor.morphism_of(UINT64_C(4), UINT64_C(7), UINT64_C(3)));
  static inline const uint64_t roundtrip_left_11 = crane::any_cast<uint64_t>(
      compose_functor<
          typename toy_prestable::base_category,
          typename opposite_prestable_category<
              opposite_prestable_category<toy_prestable>>::base_category,
          typename toy_prestable::base_category>(backward_functor,
                                                 forward_functor)
          .object_of(UINT64_C(11)));
  static inline const uint64_t roundtrip_right_13 = crane::any_cast<uint64_t>(
      compose_functor<
          typename opposite_prestable_category<
              opposite_prestable_category<toy_prestable>>::base_category,
          typename toy_prestable::base_category,
          typename opposite_prestable_category<
              opposite_prestable_category<toy_prestable>>::base_category>(
          forward_functor, backward_functor)
          .object_of(UINT64_C(13)));
  static inline const uint64_t roundtrip_morphism_5 = crane::any_cast<uint64_t>(
      compose_functor<
          typename toy_prestable::base_category,
          typename opposite_prestable_category<
              opposite_prestable_category<toy_prestable>>::base_category,
          typename toy_prestable::base_category>(backward_functor,
                                                 forward_functor)
          .morphism_of(UINT64_C(2), UINT64_C(9), UINT64_C(5)));
  static inline const uint64_t left_identity_code_11 = path_code<uint64_t>(
      crane::any_cast<uint64_t>(
          compose_functor<
              typename toy_prestable::base_category,
              typename opposite_prestable_category<
                  opposite_prestable_category<toy_prestable>>::base_category,
              typename toy_prestable::base_category>(
              backward_package.projT1(), toy_duality_involution.projT1())
              .object_of(UINT64_C(11))),
      UINT64_C(11), identity_witnesses.first(UINT64_C(11)));
  static inline const uint64_t right_identity_code_13 = path_code<uint64_t>(
      crane::any_cast<uint64_t>(
          compose_functor<
              typename opposite_prestable_category<
                  opposite_prestable_category<toy_prestable>>::base_category,
              typename toy_prestable::base_category,
              typename opposite_prestable_category<
                  opposite_prestable_category<toy_prestable>>::base_category>(
              toy_duality_involution.projT1(), backward_package.projT1())
              .object_of(UINT64_C(13))),
      UINT64_C(13), identity_witnesses.second(UINT64_C(13)));
  static inline const uint64_t suspended_zero = crane::any_cast<uint64_t>(
      toy_prestable::suspension(toy_prestable::zero_object()));
};

#endif // INCLUDED_DOUBLE_OPPOSITE_WITNESSES
