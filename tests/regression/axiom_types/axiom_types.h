#ifndef INCLUDED_AXIOM_TYPES
#define INCLUDED_AXIOM_TYPES

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct AxiomTypes {
  using MysteryType = std::any /* AXIOM TO BE REALIZED */;
  static MysteryType mystery_value();
  static MysteryType mystery_function(const MysteryType _x0);
  static MysteryType use_axiom(const std::monostate _x);

  struct AxiomRecord {
    unsigned int normal_field;
    MysteryType axiom_field;
  };

  static std::shared_ptr<AxiomRecord>
  make_axiom_record(const std::monostate _x);
  static MysteryType extract_axiom_field(const std::shared_ptr<AxiomRecord> &r);

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

  public:
    // CREATORS
    explicit AxiomInductive(AxConstr1 _v) : d_v_(std::move(_v)) {}

    explicit AxiomInductive(AxConstr2 _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<AxiomInductive> axconstr1(unsigned int a0) {
      return std::make_shared<AxiomInductive>(AxConstr1{std::move(a0)});
    }

    static std::shared_ptr<AxiomInductive> axconstr2(MysteryType a0) {
      return std::make_shared<AxiomInductive>(AxConstr2{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, MysteryType> F1>
  static T1 AxiomInductive_rect(F0 &&f, F1 &&f0,
                                const std::shared_ptr<AxiomInductive> &a) {
    if (std::holds_alternative<typename AxiomInductive::AxConstr1>(a->v())) {
      const auto &_m =
          *std::get_if<typename AxiomInductive::AxConstr1>(&a->v());
      return f(_m.d_a0);
    } else {
      const auto &_m =
          *std::get_if<typename AxiomInductive::AxConstr2>(&a->v());
      return f0(_m.d_a0);
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, MysteryType> F1>
  static T1 AxiomInductive_rec(F0 &&f, F1 &&f0,
                               const std::shared_ptr<AxiomInductive> &a) {
    if (std::holds_alternative<typename AxiomInductive::AxConstr1>(a->v())) {
      const auto &_m =
          *std::get_if<typename AxiomInductive::AxConstr1>(&a->v());
      return f(_m.d_a0);
    } else {
      const auto &_m =
          *std::get_if<typename AxiomInductive::AxConstr2>(&a->v());
      return f0(_m.d_a0);
    }
  }

  static std::shared_ptr<AxiomInductive>
  use_axiom_inductive(const std::monostate _x);
  static MysteryType axiom_identity(const MysteryType x);
  static MysteryType nested_axiom(const std::monostate _x);

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

  public:
    // CREATORS
    explicit list(Nil _v) : d_v_(_v) {}

    explicit list(Cons _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<list<t_A>> nil() {
      return std::make_shared<list<t_A>>(Nil{});
    }

    static std::shared_ptr<list<t_A>>
    cons(t_A a0, const std::shared_ptr<list<t_A>> &a1) {
      return std::make_shared<list<t_A>>(Cons{std::move(a0), a1});
    }

    static std::shared_ptr<list<t_A>> cons(t_A a0,
                                           std::shared_ptr<list<t_A>> &&a1) {
      return std::make_shared<list<t_A>>(Cons{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<list<T1>>, T2> F1>
  static T2 list_rect(const T2 f, F1 &&f0, const std::shared_ptr<list<T1>> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l->v())) {
      return f;
    } else {
      const auto &_m = *std::get_if<typename list<T1>::Cons>(&l->v());
      return f0(_m.d_a0, _m.d_a1, list_rect<T1, T2>(f, f0, _m.d_a1));
    }
  }

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<list<T1>>, T2> F1>
  static T2 list_rec(const T2 f, F1 &&f0, const std::shared_ptr<list<T1>> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l->v())) {
      return f;
    } else {
      const auto &_m = *std::get_if<typename list<T1>::Cons>(&l->v());
      return f0(_m.d_a0, _m.d_a1, list_rec<T1, T2>(f, f0, _m.d_a1));
    }
  }

  static std::shared_ptr<list<MysteryType>> axiom_list(const std::monostate _x);

  template <typename T1> static T1 poly_axiom(const T1 x) { return x; }

  static MysteryType use_poly_axiom(const std::monostate _x);
};

#endif // INCLUDED_AXIOM_TYPES
