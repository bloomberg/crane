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

enum class unit { tt };

struct AxiomTypes {
  using MysteryType = std::any /* AXIOM TO BE REALIZED */;
  static MysteryType mystery_value();
  static MysteryType mystery_function(const MysteryType _x0);
  static MysteryType use_axiom(const unit _x);

  struct AxiomRecord {
    unsigned int normal_field;
    MysteryType axiom_field;
  };

  static std::shared_ptr<AxiomRecord> make_axiom_record(const unit _x);
  static MysteryType extract_axiom_field(const std::shared_ptr<AxiomRecord> &r);

  struct AxiomInductive {
  public:
    struct AxConstr1 {
      unsigned int _a0;
    };

    struct AxConstr2 {
      MysteryType _a0;
    };

    using variant_t = std::variant<AxConstr1, AxConstr2>;

  private:
    variant_t v_;

    explicit AxiomInductive(AxConstr1 _v) : v_(std::move(_v)) {}

    explicit AxiomInductive(AxConstr2 _v) : v_(std::move(_v)) {}

  public:
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

    const variant_t &v() const { return v_; }

    variant_t &v_mut() { return v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, MysteryType> F1>
  static T1 AxiomInductive_rect(F0 &&f, F1 &&f0,
                                const std::shared_ptr<AxiomInductive> &a) {
    return std::visit(
        Overloaded{[&](const typename AxiomInductive::AxConstr1 _args) -> T1 {
                     unsigned int n = _args._a0;
                     return f(std::move(n));
                   },
                   [&](const typename AxiomInductive::AxConstr2 _args) -> T1 {
                     MysteryType m = _args._a0;
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
                     unsigned int n = _args._a0;
                     return f(std::move(n));
                   },
                   [&](const typename AxiomInductive::AxConstr2 _args) -> T1 {
                     MysteryType m = _args._a0;
                     return f0(m);
                   }},
        a->v());
  }

  static std::shared_ptr<AxiomInductive> use_axiom_inductive(const unit _x);
  static MysteryType axiom_identity(const MysteryType x);
  static MysteryType nested_axiom(const unit _x);

  template <typename A> struct list {
  public:
    struct nil {};

    struct cons {
      A _a0;
      std::shared_ptr<list<A>> _a1;
    };

    using variant_t = std::variant<nil, cons>;

  private:
    variant_t v_;

    explicit list(nil _v) : v_(std::move(_v)) {}

    explicit list(cons _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<list<A>> nil_() {
        return std::shared_ptr<list<A>>(new list<A>(nil{}));
      }

      static std::shared_ptr<list<A>>
      cons_(A a0, const std::shared_ptr<list<A>> &a1) {
        return std::shared_ptr<list<A>>(new list<A>(cons{a0, a1}));
      }

      static std::unique_ptr<list<A>> nil_uptr() {
        return std::unique_ptr<list<A>>(new list<A>(nil{}));
      }

      static std::unique_ptr<list<A>>
      cons_uptr(A a0, const std::shared_ptr<list<A>> &a1) {
        return std::unique_ptr<list<A>>(new list<A>(cons{a0, a1}));
      }
    };

    const variant_t &v() const { return v_; }

    variant_t &v_mut() { return v_; }
  };

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<list<T1>>, T2> F1>
  static T2 list_rect(const T2 f, F1 &&f0, const std::shared_ptr<list<T1>> &l) {
    return std::visit(
        Overloaded{[&](const typename list<T1>::nil _args) -> T2 { return f; },
                   [&](const typename list<T1>::cons _args) -> T2 {
                     T1 y = _args._a0;
                     std::shared_ptr<list<T1>> l0 = _args._a1;
                     return f0(y, l0, list_rect<T1, T2>(f, f0, l0));
                   }},
        l->v());
  }

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<list<T1>>, T2> F1>
  static T2 list_rec(const T2 f, F1 &&f0, const std::shared_ptr<list<T1>> &l) {
    return std::visit(
        Overloaded{[&](const typename list<T1>::nil _args) -> T2 { return f; },
                   [&](const typename list<T1>::cons _args) -> T2 {
                     T1 y = _args._a0;
                     std::shared_ptr<list<T1>> l0 = _args._a1;
                     return f0(y, l0, list_rec<T1, T2>(f, f0, l0));
                   }},
        l->v());
  }

  static std::shared_ptr<list<MysteryType>> axiom_list(const unit _x);

  template <typename T1> static T1 poly_axiom(const T1 x) { return x; }

  static MysteryType use_poly_axiom(const unit _x);
};
