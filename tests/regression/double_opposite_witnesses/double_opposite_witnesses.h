#ifndef INCLUDED_DOUBLE_OPPOSITE_WITNESSES
#define INCLUDED_DOUBLE_OPPOSITE_WITNESSES

#include <any>
#include <concepts>
#include <functional>
#include <utility>
#include <variant>

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

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
  } -> std::convertible_to<std::any>;
  {
    I::compose(std::declval<typename I::Obj>(), std::declval<typename I::Obj>(),
               std::declval<typename I::Obj>(), std::declval<std::any>(),
               std::declval<std::any>())
  } -> std::convertible_to<std::any>;
};
template <typename I>
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
  static T2 Path_rec(const T1 &, T2 f, const T1 &, const Path<T1> &) {
    return f;
  }

  template <typename T1>
  static uint64_t path_code(const T1 &, const T1 &, const Path<T1> &) {
    return UINT64_C(1);
  }

  using Obj = std::any;
  using Hom = std::any;

  template <PreCategory _tcI0> struct opposite_category {
    using Obj = typename _tcI0::Obj;

    static std::any identity(Obj x) { return _tcI0::identity(x); }

    static std::any compose(Obj x, Obj y, Obj z, std::any f, std::any g) {
      return _tcI0::compose(z, y, x, g, f);
    }
  };

  struct Functor {
    std::function<Obj(Obj)> object_of;
    std::function<Hom(Obj, Obj, Hom)> morphism_of;
  };

  template <PreCategory _tcI0, PreCategory _tcI1, PreCategory _tcI2>
  static Functor compose_functor(Functor f, Functor g) {
    return Functor{
        [=](const auto &x) mutable { return f.object_of(g.object_of(x)); },
        [=](const auto &x, const auto &y, const auto &f0) mutable {
          return f.morphism_of(g.object_of(x), g.object_of(y),
                               g.morphism_of(x, y, f0));
        }};
  }

  template <PreStableCategory _tcI0> struct opposite_prestable_category {
    using base_category = opposite_category<typename _tcI0::base_category>;
    using Obj = typename base_category::Obj;

    static Obj zero_object() { return _tcI0::zero_object(); }

    static Obj suspension(std::any x) { return _tcI0::suspension(x); }
  };

  struct nat_category {
    using Obj = uint64_t;

    static std::any identity(uint64_t x) { return x; }

    static std::any compose(uint64_t, uint64_t, uint64_t, std::any f,
                            std::any g) {
      return (std::any_cast<uint64_t>(std::move(f)) +
              std::any_cast<uint64_t>(std::move(g)));
    }
  };

  static_assert(PreCategory<nat_category>);

  struct toy_prestable {
    using base_category = nat_category;
    using Obj = typename base_category::Obj;

    static Obj zero_object() { return UINT64_C(0); }

    static Obj suspension(uint64_t x) { return (std::move(x) + 1); }
  };

  static_assert(PreStableCategory<toy_prestable>);

  template <PreCategory _tcI0> static Functor into_double_opposite_functor() {
    return Functor{[](const auto &x) { return x; },
                   [](const auto &, const auto &, const auto &f) { return f; }};
  }

  template <PreCategory _tcI0> static Functor out_of_double_opposite_functor() {
    return Functor{[](const auto &x) { return x; },
                   [](const auto &, const auto &, const auto &f) { return f; }};
  }

  template <PreStableCategory _tcI0>
  static SigT<
      Functor,
      SigT<Functor,
           std::pair<std::function<Path<typename _tcI0::base_category::Obj>(
                         typename _tcI0::base_category::Obj)>,
                     std::function<Path<typename _tcI0::base_category::Obj>(
                         typename _tcI0::base_category::Obj)>>>>
  duality_involution() {
    return SigT<
        Functor,
        SigT<Functor,
             std::pair<std::function<Path<typename _tcI0::base_category::Obj>(
                           typename _tcI0::base_category::Obj)>,
                       std::function<Path<typename _tcI0::base_category::Obj>(
                           typename _tcI0::base_category::Obj)>>>>::
        existt(
            into_double_opposite_functor<typename _tcI0::base_category>(),
            SigT<Functor,
                 std::pair<
                     std::function<Path<typename _tcI0::base_category::Obj>(
                         typename _tcI0::base_category::Obj)>,
                     std::function<Path<typename _tcI0::base_category::Obj>(
                         typename _tcI0::base_category::Obj)>>>::
                existt(
                    out_of_double_opposite_functor<
                        typename _tcI0::base_category>(),
                    std::make_pair(
                        [](const typename _tcI0::base_category::Obj &) {
                          return Path<
                              typename _tcI0::base_category::Obj>::path_refl();
                        },
                        [](const typename _tcI0::base_category::Obj &) {
                          return Path<
                              typename _tcI0::base_category::Obj>::path_refl();
                        })));
  }

  static inline const SigT<
      Functor,
      SigT<Functor, std::pair<std::function<Path<uint64_t>(uint64_t)>,
                              std::function<Path<uint64_t>(uint64_t)>>>>
      toy_duality_involution = std::any_cast<SigT<
          Functor,
          SigT<Functor, std::pair<std::function<Path<uint64_t>(uint64_t)>,
                                  std::function<Path<uint64_t>(uint64_t)>>>>>(
          duality_involution<toy_prestable>());
  static inline const Functor forward_functor = toy_duality_involution.projT1();
  static inline const SigT<Functor,
                           std::pair<std::function<Path<uint64_t>(uint64_t)>,
                                     std::function<Path<uint64_t>(uint64_t)>>>
      backward_package = toy_duality_involution.projT2();
  static inline const Functor backward_functor = backward_package.projT1();
  static inline const std::pair<std::function<Path<uint64_t>(uint64_t)>,
                                std::function<Path<uint64_t>(uint64_t)>>
      identity_witnesses = backward_package.projT2();
  static inline const uint64_t forward_object_7 =
      std::any_cast<uint64_t>(forward_functor.object_of(UINT64_C(7)));
  static inline const uint64_t backward_object_9 =
      std::any_cast<uint64_t>(backward_functor.object_of(UINT64_C(9)));
  static inline const uint64_t forward_morphism_3 = std::any_cast<uint64_t>(
      forward_functor.morphism_of(UINT64_C(4), UINT64_C(7), UINT64_C(3)));
  static inline const uint64_t roundtrip_left_11 = std::any_cast<uint64_t>(
      compose_functor<
          typename toy_prestable::base_category,
          typename opposite_prestable_category<
              opposite_prestable_category<toy_prestable>>::base_category,
          typename toy_prestable::base_category>(backward_functor,
                                                 forward_functor)
          .object_of(UINT64_C(11)));
  static inline const uint64_t roundtrip_right_13 = std::any_cast<uint64_t>(
      compose_functor<
          typename opposite_prestable_category<
              opposite_prestable_category<toy_prestable>>::base_category,
          typename toy_prestable::base_category,
          typename opposite_prestable_category<
              opposite_prestable_category<toy_prestable>>::base_category>(
          forward_functor, backward_functor)
          .object_of(UINT64_C(13)));
  static inline const uint64_t roundtrip_morphism_5 = std::any_cast<uint64_t>(
      compose_functor<
          typename toy_prestable::base_category,
          typename opposite_prestable_category<
              opposite_prestable_category<toy_prestable>>::base_category,
          typename toy_prestable::base_category>(backward_functor,
                                                 forward_functor)
          .morphism_of(UINT64_C(2), UINT64_C(9), UINT64_C(5)));
  static inline const uint64_t left_identity_code_11 = path_code<uint64_t>(
      std::any_cast<uint64_t>(
          compose_functor<
              typename toy_prestable::base_category,
              typename opposite_prestable_category<
                  opposite_prestable_category<toy_prestable>>::base_category,
              typename toy_prestable::base_category>(
              backward_package.projT1(), toy_duality_involution.projT1())
              .object_of(UINT64_C(11))),
      UINT64_C(11), identity_witnesses.first(UINT64_C(11)));
  static inline const uint64_t right_identity_code_13 = path_code<uint64_t>(
      std::any_cast<uint64_t>(
          compose_functor<
              typename opposite_prestable_category<
                  opposite_prestable_category<toy_prestable>>::base_category,
              typename toy_prestable::base_category,
              typename opposite_prestable_category<
                  opposite_prestable_category<toy_prestable>>::base_category>(
              toy_duality_involution.projT1(), backward_package.projT1())
              .object_of(UINT64_C(13))),
      UINT64_C(13), identity_witnesses.second(UINT64_C(13)));
  static inline const uint64_t suspended_zero = std::any_cast<uint64_t>(
      toy_prestable::suspension(toy_prestable::zero_object()));
};

#endif // INCLUDED_DOUBLE_OPPOSITE_WITNESSES
