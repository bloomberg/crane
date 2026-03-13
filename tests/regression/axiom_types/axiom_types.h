#ifndef INCLUDED_AXIOM_TYPES
#define INCLUDED_AXIOM_TYPES

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

enum class Unit { e_TT };

struct AxiomTypes {
  using MysteryType = std::any /* AXIOM TO BE REALIZED */;
  __attribute__((pure)) static MysteryType mystery_value();
  __attribute__((pure)) static MysteryType
  mystery_function(const MysteryType _x0);
  __attribute__((pure)) static MysteryType use_axiom(const Unit _x);

  struct AxiomRecord {
    unsigned int normal_field;
    MysteryType axiom_field;
  };

  static std::shared_ptr<AxiomRecord> make_axiom_record(const Unit _x);
  __attribute__((pure)) static MysteryType
  extract_axiom_field(const std::shared_ptr<AxiomRecord> &r);

  struct AxiomInductive {
    // TYPES
    struct AxConstr1 {
      unsigned int d_a0;
    };

    struct AxConstr2 {
      MysteryType d_a0;
    };

    using variant_t = std::variant<AxConstr1, AxConstr2>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit AxiomInductive(AxConstr1 _v) : d_v_(std::move(_v)) {}

    explicit AxiomInductive(AxConstr2 _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<AxiomInductive> AxConstr1_(unsigned int a0) {
        return std::shared_ptr<AxiomInductive>(
            new AxiomInductive(AxConstr1{a0}));
      }

      static std::shared_ptr<AxiomInductive> AxConstr2_(MysteryType a0) {
        return std::shared_ptr<AxiomInductive>(
            new AxiomInductive(AxConstr2{a0}));
      }

      static std::unique_ptr<AxiomInductive> AxConstr1_uptr(unsigned int a0) {
        return std::unique_ptr<AxiomInductive>(
            new AxiomInductive(AxConstr1{a0}));
      }

      static std::unique_ptr<AxiomInductive> AxConstr2_uptr(MysteryType a0) {
        return std::unique_ptr<AxiomInductive>(
            new AxiomInductive(AxConstr2{a0}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, MysteryType> F1>
  static T1 AxiomInductive_rect(F0 &&f, F1 &&f0,
                                const std::shared_ptr<AxiomInductive> &a) {
    return std::visit(
        Overloaded{[&](const typename AxiomInductive::AxConstr1 _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     return f(std::move(n));
                   },
                   [&](const typename AxiomInductive::AxConstr2 _args) -> T1 {
                     MysteryType m = _args.d_a0;
                     return f0(m);
                   }},
        a->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, MysteryType> F1>
  static T1 AxiomInductive_rec(F0 &&f, F1 &&f0,
                               const std::shared_ptr<AxiomInductive> &a) {
    return std::visit(
        Overloaded{[&](const typename AxiomInductive::AxConstr1 _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     return f(std::move(n));
                   },
                   [&](const typename AxiomInductive::AxConstr2 _args) -> T1 {
                     MysteryType m = _args.d_a0;
                     return f0(m);
                   }},
        a->v());
  }

  static std::shared_ptr<AxiomInductive> use_axiom_inductive(const Unit _x);
  __attribute__((pure)) static MysteryType axiom_identity(const MysteryType x);
  __attribute__((pure)) static MysteryType nested_axiom(const Unit _x);

  template <typename t_A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      t_A d_a0;
      std::shared_ptr<list<t_A>> d_a1;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit list(Nil _v) : d_v_(std::move(_v)) {}

    explicit list(Cons _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<list<t_A>> Nil_() {
        return std::shared_ptr<list<t_A>>(new list<t_A>(Nil{}));
      }

      static std::shared_ptr<list<t_A>>
      Cons_(t_A a0, const std::shared_ptr<list<t_A>> &a1) {
        return std::shared_ptr<list<t_A>>(new list<t_A>(Cons{a0, a1}));
      }

      static std::unique_ptr<list<t_A>> Nil_uptr() {
        return std::unique_ptr<list<t_A>>(new list<t_A>(Nil{}));
      }

      static std::unique_ptr<list<t_A>>
      Cons_uptr(t_A a0, const std::shared_ptr<list<t_A>> &a1) {
        return std::unique_ptr<list<t_A>>(new list<t_A>(Cons{a0, a1}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<list<T1>>, T2> F1>
  static T2 list_rect(const T2 f, F1 &&f0, const std::shared_ptr<list<T1>> &l) {
    return std::visit(
        Overloaded{[&](const typename list<T1>::Nil _args) -> T2 { return f; },
                   [&](const typename list<T1>::Cons _args) -> T2 {
                     T1 y = _args.d_a0;
                     std::shared_ptr<list<T1>> l0 = _args.d_a1;
                     return f0(y, l0, list_rect<T1, T2>(f, f0, l0));
                   }},
        l->v());
  }

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<list<T1>>, T2> F1>
  static T2 list_rec(const T2 f, F1 &&f0, const std::shared_ptr<list<T1>> &l) {
    return std::visit(
        Overloaded{[&](const typename list<T1>::Nil _args) -> T2 { return f; },
                   [&](const typename list<T1>::Cons _args) -> T2 {
                     T1 y = _args.d_a0;
                     std::shared_ptr<list<T1>> l0 = _args.d_a1;
                     return f0(y, l0, list_rec<T1, T2>(f, f0, l0));
                   }},
        l->v());
  }

  static std::shared_ptr<list<MysteryType>> axiom_list(const Unit _x);

  template <typename T1> static T1 poly_axiom(const T1 x) { return x; }

  __attribute__((pure)) static MysteryType use_poly_axiom(const Unit _x);
};

#endif // INCLUDED_AXIOM_TYPES
