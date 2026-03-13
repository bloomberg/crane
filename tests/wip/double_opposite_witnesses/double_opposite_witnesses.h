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
          t_A a = _args.d_a0;
          return a;
        }},
        this->v());
  }

  t_P projT2() const {
    return std::visit(
        Overloaded{[](const typename SigT<t_A, t_P>::ExistT _args) -> t_P {
          t_P h = _args.d_a1;
          return h;
        }},
        this->v());
  }
};

template <typename I>
concept PreCategory = requires(typename I::Obj a0, typename I::Obj a1,
                               typename I::Obj a2, std::any a3, std::any a4) {
  typename I::Obj;
  { I::identity(a0) } -> std::convertible_to<std::any>;
  { I::compose(a4, a3, a2, a1, a0) } -> std::convertible_to<std::any>;
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

  template <typename _tcI0> struct opposite_category {
    static std::any identity(Obj X) { return _tcI0::identity(x); }

    static std::any compose(Obj X, Obj Y, Obj Z, std::any f, std::any g) {
      return _tcI0::compose(z, y, x, g, f);
    }
  };

  struct Functor {
    std::function<Obj(Obj)> object_of;
    std::function<Hom(Obj, Obj, Hom)> morphism_of;
  };

  template <typename _tcI0, typename _tcI1, typename _tcI2>
  static std::shared_ptr<Functor> compose_functor(std::shared_ptr<Functor> f,
                                                  std::shared_ptr<Functor> g) {
    return std::make_shared<Functor>(
        Functor{[=](Obj x) mutable { return f->object_of(g->object_of(x)); },
                [=](Obj x, Obj y, Obj f0) mutable {
                  return f->morphism_of(g->object_of(x), g->object_of(y),
                                        g->morphism_of(x, y, f0));
                }});
  }

  struct PreStableCategory {
    std::shared_ptr<PreCategory> base_category;
    Obj zero_object;
    std::function<Obj(Obj)> suspension;
  };

  static std::shared_ptr<PreStableCategory>
  opposite_prestable_category(std::shared_ptr<PreStableCategory> pS);

  struct nat_category {
    static std::any identity(unsigned int X) { return std::move(x); }

    static std::any compose(unsigned int _x, unsigned int _x, unsigned int _x,
                            std::any f, std::any g) {
      return (f + std::move(g));
    }
  };

  static_assert(PreCategory<nat_category>);
  static inline const std::shared_ptr<PreStableCategory> toy_prestable =
      std::make_shared<PreStableCategory>(PreStableCategory{
          nat_category, 0u, [](unsigned int x) { return (x + 1); }});

  template <typename _tcI0>
  static std::shared_ptr<Functor> into_double_opposite_functor() {
    return std::make_shared<Functor>(Functor{
        [](Obj x) { return x; }, [](Obj _x, Obj _x0, Obj f) { return f; }});
  }

  template <typename _tcI0>
  static std::shared_ptr<Functor> out_of_double_opposite_functor() {
    return std::make_shared<Functor>(Functor{
        [](Obj x) { return x; }, [](Obj _x, Obj _x0, Obj f) { return f; }});
  }

  template <typename Obj>
  static std::shared_ptr<
      SigT<std::shared_ptr<Functor>,
           std::shared_ptr<SigT<
               std::shared_ptr<Functor>,
               std::pair<std::function<std::shared_ptr<Path<Obj>>(Obj)>,
                         std::function<std::shared_ptr<Path<Obj>>(Obj)>>>>>>
  duality_involution(std::shared_ptr<PreStableCategory> pS) {
    return SigT<
        std::shared_ptr<Functor>,
        std::shared_ptr<SigT<
            std::shared_ptr<Functor>,
            std::pair<
                std::function<std::shared_ptr<Path<std::any>>(std::any)>,
                std::function<std::shared_ptr<Path<std::any>>(std::any)>>>>>::
        ctor::ExistT_(
            into_double_opposite_functor(pS->base_category),
            SigT<
                std::shared_ptr<Functor>,
                std::pair<
                    std::function<std::shared_ptr<Path<std::any>>(std::any)>,
                    std::function<std::shared_ptr<Path<std::any>>(std::any)>>>::
                ctor::ExistT_(out_of_double_opposite_functor(pS->base_category),
                              std::make_pair(
                                  [](std::any _x) {
                                    return Path<std::any>::ctor::Path_refl_();
                                  },
                                  [](std::any _x) {
                                    return Path<std::any>::ctor::Path_refl_();
                                  })));
  }

  template <typename Obj>
  static const std::shared_ptr<
      SigT<std::shared_ptr<Functor>,
           std::shared_ptr<SigT<
               std::shared_ptr<Functor>,
               std::pair<std::function<std::shared_ptr<Path<Obj>>(Obj)>,
                         std::function<std::shared_ptr<Path<Obj>>(Obj)>>>>>> &
  toy_duality_involution() {
    static const std::shared_ptr<
        SigT<std::shared_ptr<Functor>,
             std::shared_ptr<SigT<
                 std::shared_ptr<Functor>,
                 std::pair<std::function<std::shared_ptr<Path<Obj>>(Obj)>,
                           std::function<std::shared_ptr<Path<Obj>>(Obj)>>>>>>
        v = duality_involution(toy_prestable);
    return v;
  }

  static inline const std::shared_ptr<Functor> forward_functor =
      toy_duality_involution()->projT1();

  template <typename Obj>
  static const std::shared_ptr<
      SigT<std::shared_ptr<Functor>,
           std::pair<std::function<std::shared_ptr<Path<Obj>>(Obj)>,
                     std::function<std::shared_ptr<Path<Obj>>(Obj)>>>> &
  backward_package() {
    static const std::shared_ptr<
        SigT<std::shared_ptr<Functor>,
             std::pair<std::function<std::shared_ptr<Path<Obj>>(Obj)>,
                       std::function<std::shared_ptr<Path<Obj>>(Obj)>>>>
        v = toy_duality_involution()->projT2();
    return v;
  }

  static inline const std::shared_ptr<Functor> backward_functor =
      backward_package()->projT1();

  template <typename Obj>
  static const std::pair<std::function<std::shared_ptr<Path<Obj>>(Obj)>,
                         std::function<std::shared_ptr<Path<Obj>>(Obj)>> &
  identity_witnesses() {
    static const std::pair<std::function<std::shared_ptr<Path<Obj>>(Obj)>,
                           std::function<std::shared_ptr<Path<Obj>>(Obj)>>
        v = backward_package()->projT2();
    return v;
  }

  static inline const unsigned int forward_object_7 =
      forward_functor->object_of(7u);
  static inline const unsigned int backward_object_9 =
      backward_functor->object_of(9u);
  static inline const unsigned int forward_morphism_3 =
      forward_functor->morphism_of(4u, 7u, 3u);
  static inline const unsigned int roundtrip_left_11 =
      compose_functor(toy_prestable->base_category,
                      opposite_prestable_category(
                          opposite_prestable_category(toy_prestable))
                          ->base_category,
                      toy_prestable->base_category, backward_functor,
                      forward_functor)
          ->object_of(11u);
  static inline const unsigned int roundtrip_right_13 =
      compose_functor(opposite_prestable_category(
                          opposite_prestable_category(toy_prestable))
                          ->base_category,
                      toy_prestable->base_category,
                      opposite_prestable_category(
                          opposite_prestable_category(toy_prestable))
                          ->base_category,
                      forward_functor, backward_functor)
          ->object_of(13u);
  static inline const unsigned int roundtrip_morphism_5 =
      compose_functor(toy_prestable->base_category,
                      opposite_prestable_category(
                          opposite_prestable_category(toy_prestable))
                          ->base_category,
                      toy_prestable->base_category, backward_functor,
                      forward_functor)
          ->morphism_of(2u, 9u, 5u);
  static inline const unsigned int left_identity_code_11 = path_code<Obj>(
      compose_functor(toy_prestable->base_category,
                      opposite_prestable_category(
                          opposite_prestable_category(toy_prestable))
                          ->base_category,
                      toy_prestable->base_category,
                      backward_package()->projT1(),
                      toy_duality_involution()->projT1())
          ->object_of(11u),
      11u, ([]() -> std::any {
        throw std::logic_error("untranslatable curried proof term");
        return std::any{};
      })());
  static inline const unsigned int right_identity_code_13 = path_code<Obj>(
      compose_functor(opposite_prestable_category(
                          opposite_prestable_category(toy_prestable))
                          ->base_category,
                      toy_prestable->base_category,
                      opposite_prestable_category(
                          opposite_prestable_category(toy_prestable))
                          ->base_category,
                      toy_duality_involution()->projT1(),
                      backward_package()->projT1())
          ->object_of(13u),
      13u, ([]() -> std::any {
        throw std::logic_error("untranslatable curried proof term");
        return std::any{};
      })());
  static inline const unsigned int suspended_zero =
      toy_prestable->suspension(toy_prestable->zero_object);
};

#endif // INCLUDED_DOUBLE_OPPOSITE_WITNESSES
