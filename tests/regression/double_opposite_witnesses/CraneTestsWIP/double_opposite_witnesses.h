#ifndef INCLUDED_DOUBLE_OPPOSITE_WITNESSES
#define INCLUDED_DOUBLE_OPPOSITE_WITNESSES

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename t_A, typename t_P> struct SigT {
  // TYPES
  struct ExistT {
    t_A d_a0;
    t_P d_a1;
  };

  using variant_t = std::variant<ExistT>;

private:
  // DATA
  variant_t d_v_;

  // CREATORS
  explicit SigT(ExistT _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<SigT<t_A, t_P>> ExistT_(t_A a0, t_P a1) {
      return std::shared_ptr<SigT<t_A, t_P>>(
          new SigT<t_A, t_P>(ExistT{a0, a1}));
    }

    static std::unique_ptr<SigT<t_A, t_P>> ExistT_uptr(t_A a0, t_P a1) {
      return std::unique_ptr<SigT<t_A, t_P>>(
          new SigT<t_A, t_P>(ExistT{a0, a1}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  t_A projT1() const {
    return std::visit(
        Overloaded{[](const typename SigT<t_A, t_P>::ExistT _args) -> t_A {
          return _args.d_a0;
        }},
        this->v());
  }

  t_P projT2() const {
    return std::visit(
        Overloaded{[](const typename SigT<t_A, t_P>::ExistT _args) -> t_P {
          return _args.d_a1;
        }},
        this->v());
  }
};

template <typename I>
concept PreCategory =
    requires(typename I::Obj a0, typename I::Obj a1, typename I::Obj a2,
             typename I::Hom a3, typename I::Hom a4) {
      typename I::Hom;
      typename I::Obj;
      { I::identity(a0) } -> std::convertible_to<typename I::Hom>;
      {
        I::compose(a0, a1, a2, a3, a4)
      } -> std::convertible_to<typename I::Hom>;
    };
template <typename I>
concept PreStableCategory = requires(typename I::base_category::Obj a0) {
  typename I::base_category;
  { I::zero_object() } -> std::convertible_to<typename I::base_category::Obj>;
  { I::suspension(a0) } -> std::convertible_to<typename I::base_category::Obj>;
};

struct DoubleOppositeWitnessesCase {
  template <typename t_A> struct Path {
    // TYPES
    struct Path_refl {};

    using variant_t = std::variant<Path_refl>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit Path(Path_refl _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<Path<t_A>> Path_refl_() {
        return std::shared_ptr<Path<t_A>>(new Path<t_A>(Path_refl{}));
      }

      static std::unique_ptr<Path<t_A>> Path_refl_uptr() {
        return std::unique_ptr<Path<t_A>>(new Path<t_A>(Path_refl{}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2>
  static T2 Path_rect(const T1 _x, const T2 f, const T1 _x0,
                      const std::shared_ptr<Path<T1>> &p) {
    return std::visit(
        Overloaded{
            [&](const typename Path<T1>::Path_refl _args) -> T2 { return f; }},
        p->v());
  }

  template <typename T1, typename T2>
  static T2 Path_rec(const T1 _x, const T2 f, const T1 _x0,
                     const std::shared_ptr<Path<T1>> &p) {
    return std::visit(
        Overloaded{
            [&](const typename Path<T1>::Path_refl _args) -> T2 { return f; }},
        p->v());
  }

  template <typename T1>
  __attribute__((pure)) static unsigned int
  path_code(const T1 _x, const T1 _x0, const std::shared_ptr<Path<T1>> &p) {
    return std::visit(Overloaded{[](const typename Path<T1>::Path_refl _args)
                                     -> unsigned int { return 1u; }},
                      p->v());
  }

  using Obj = std::any;
  using Hom = std::any;

  template <PreCategory _tcI0> struct opposite_category {
    using Hom = typename _tcI0::Hom;
    using Obj = typename _tcI0::Obj;

    static Obj identity(Hom x) { return _tcI0::identity(x); }

    static Obj compose(Hom x, Hom y, Hom z, Obj f, Obj g) {
      return _tcI0::compose(z, y, x, g, f);
    }
  };

  struct Functor {
    std::function<Obj(Obj)> object_of;
    std::function<Hom(Obj, Obj, Hom)> morphism_of;
  };

  template <PreCategory _tcI0, PreCategory _tcI1, PreCategory _tcI2>
  static std::shared_ptr<Functor> compose_functor(std::shared_ptr<Functor> f,
                                                  std::shared_ptr<Functor> g) {
    return std::make_shared<Functor>(Functor{
        [=](std::any x) mutable { return f->object_of(g->object_of(x)); },
        [=](std::any x, std::any y, std::any f0) mutable {
          return f->morphism_of(g->object_of(x), g->object_of(y),
                                g->morphism_of(x, y, f0));
        }});
  }

  template <PreStableCategory _tcI0> struct opposite_prestable_category {
    using base_category = opposite_category<typename _tcI0::base_category>;
    using Hom = typename base_category::Hom;
    using Obj = typename base_category::Obj;

    static Obj zero_object() { return _tcI0::zero_object(); }

    static Obj suspension(std::any x) { return _tcI0::suspension(x); }
  };

  struct nat_category {
    using Hom = unsigned int;
    using Obj = unsigned int;

    __attribute__((pure)) static unsigned int identity(unsigned int x) {
      return std::move(x);
    }

    __attribute__((pure)) static unsigned int
    compose(unsigned int _x, unsigned int _x0, unsigned int _x1, unsigned int f,
            unsigned int g) {
      return (std::move(f) + std::move(g));
    }
  };

  static_assert(PreCategory<nat_category>);

  struct toy_prestable {
    using base_category = nat_category;
    using Hom = typename base_category::Hom;
    using Obj = typename base_category::Obj;

    static Obj zero_object() { return 0u; }

    static Obj suspension(unsigned int x) { return (std::move(x) + 1); }
  };

  static_assert(PreStableCategory<toy_prestable>);

  template <PreCategory _tcI0>
  static std::shared_ptr<Functor> into_double_opposite_functor() {
    return std::make_shared<Functor>(
        Functor{[](std::any x) { return x; },
                [](std::any _x, std::any _x0, std::any f) { return f; }});
  }

  template <PreCategory _tcI0>
  static std::shared_ptr<Functor> out_of_double_opposite_functor() {
    return std::make_shared<Functor>(
        Functor{[](std::any x) { return x; },
                [](std::any _x, std::any _x0, std::any f) { return f; }});
  }

  template <PreStableCategory _tcI0>
  static std::shared_ptr<
      SigT<std::shared_ptr<Functor>,
           std::shared_ptr<
               SigT<std::shared_ptr<Functor>,
                    std::pair<std::function<std::shared_ptr<
                                  Path<typename _tcI0::base_category::Obj>>(
                                  typename _tcI0::base_category::Obj)>,
                              std::function<std::shared_ptr<
                                  Path<typename _tcI0::base_category::Obj>>(
                                  typename _tcI0::base_category::Obj)>>>>>>
  duality_involution() {
    return SigT<
        std::shared_ptr<Functor>,
        std::shared_ptr<SigT<std::shared_ptr<Functor>,
                             std::pair<std::function<std::shared_ptr<
                                           Path<typename _tcI0::base_category>>(
                                           typename _tcI0::base_category)>,
                                       std::function<std::shared_ptr<
                                           Path<typename _tcI0::base_category>>(
                                           typename _tcI0::base_category)>>>>>::
        ctor::ExistT_(
            into_double_opposite_functor<typename _tcI0::base_category>(),
            SigT<std::shared_ptr<Functor>,
                 std::pair<std::function<std::shared_ptr<
                               Path<typename _tcI0::base_category>>(
                               typename _tcI0::base_category)>,
                           std::function<std::shared_ptr<
                               Path<typename _tcI0::base_category>>(
                               typename _tcI0::base_category)>>>::ctor::
                ExistT_(out_of_double_opposite_functor<
                            typename _tcI0::base_category>(),
                        std::make_pair(
                            [](typename _tcI0::base_category _x) {
                              return Path<typename _tcI0::base_category>::ctor::
                                  Path_refl_();
                            },
                            [](typename _tcI0::base_category _x) {
                              return Path<typename _tcI0::base_category>::ctor::
                                  Path_refl_();
                            })));
  }

  static inline const std::shared_ptr<
      SigT<std::shared_ptr<Functor>,
           std::shared_ptr<SigT<
               std::shared_ptr<Functor>,
               std::pair<std::function<std::shared_ptr<Path<Obj>>(Obj)>,
                         std::function<std::shared_ptr<Path<Obj>>(Obj)>>>>>>
      toy_duality_involution = duality_involution<toy_prestable>();
  static inline const std::shared_ptr<Functor> forward_functor =
      toy_duality_involution->projT1();
  static inline const std::shared_ptr<
      SigT<std::shared_ptr<Functor>,
           std::pair<std::function<std::shared_ptr<Path<Obj>>(Obj)>,
                     std::function<std::shared_ptr<Path<Obj>>(Obj)>>>>
      backward_package = toy_duality_involution->projT2();
  static inline const std::shared_ptr<Functor> backward_functor =
      backward_package->projT1();
  static inline const std::pair<std::function<std::shared_ptr<Path<Obj>>(Obj)>,
                                std::function<std::shared_ptr<Path<Obj>>(Obj)>>
      identity_witnesses = backward_package->projT2();
  static inline const unsigned int forward_object_7 =
      std::any_cast<unsigned int>(forward_functor->object_of(7u));
  static inline const unsigned int backward_object_9 =
      std::any_cast<unsigned int>(backward_functor->object_of(9u));
  static inline const unsigned int forward_morphism_3 =
      std::any_cast<unsigned int>(forward_functor->morphism_of(4u, 7u, 3u));
  static inline const unsigned int roundtrip_left_11 =
      std::any_cast<unsigned int>(
          compose_functor<
              typename toy_prestable::base_category,
              typename opposite_prestable_category<
                  opposite_prestable_category<toy_prestable>>::base_category,
              typename toy_prestable::base_category>(backward_functor,
                                                     forward_functor)
              ->object_of(11u));
  static inline const unsigned int roundtrip_right_13 =
      std::any_cast<unsigned int>(
          compose_functor<
              typename opposite_prestable_category<
                  opposite_prestable_category<toy_prestable>>::base_category,
              typename toy_prestable::base_category,
              typename opposite_prestable_category<
                  opposite_prestable_category<toy_prestable>>::base_category>(
              forward_functor, backward_functor)
              ->object_of(13u));
  static inline const unsigned int roundtrip_morphism_5 =
      std::any_cast<unsigned int>(
          compose_functor<
              typename toy_prestable::base_category,
              typename opposite_prestable_category<
                  opposite_prestable_category<toy_prestable>>::base_category,
              typename toy_prestable::base_category>(backward_functor,
                                                     forward_functor)
              ->morphism_of(2u, 9u, 5u));
  static std::shared_ptr<Path<Obj>> left_witness(const Obj _x0);
  static std::shared_ptr<Path<Obj>> right_witness(const Obj _x0);
  static inline const unsigned int left_identity_code_11 = path_code<Obj>(
      compose_functor<
          typename toy_prestable::base_category,
          typename opposite_prestable_category<
              opposite_prestable_category<toy_prestable>>::base_category,
          typename toy_prestable::base_category>(
          backward_package->projT1(), toy_duality_involution->projT1())
          ->object_of(11u),
      11u, left_witness(11u));
  static inline const unsigned int right_identity_code_13 = path_code<Obj>(
      compose_functor<
          typename opposite_prestable_category<
              opposite_prestable_category<toy_prestable>>::base_category,
          typename toy_prestable::base_category,
          typename opposite_prestable_category<
              opposite_prestable_category<toy_prestable>>::base_category>(
          toy_duality_involution->projT1(), backward_package->projT1())
          ->object_of(13u),
      13u, right_witness(13u));
  static inline const unsigned int suspended_zero = std::any_cast<unsigned int>(
      toy_prestable::suspension(toy_prestable::zero_object()));
};

#endif // INCLUDED_DOUBLE_OPPOSITE_WITNESSES
