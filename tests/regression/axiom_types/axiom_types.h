#ifndef INCLUDED_AXIOM_TYPES
#define INCLUDED_AXIOM_TYPES

#include <any>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct AxiomTypes {
  using MysteryType = std::any /* AXIOM TO BE REALIZED */;
  static MysteryType mystery_value();
  static MysteryType mystery_function(const MysteryType _x0);
  static MysteryType use_axiom(const std::monostate &_x);

  struct AxiomRecord {
    unsigned int normal_field;
    MysteryType axiom_field;

    __attribute__((pure)) AxiomRecord *operator->() { return this; }

    __attribute__((pure)) const AxiomRecord *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) AxiomRecord clone() const {
      return AxiomRecord{(*(this)).normal_field, (*(this)).axiom_field};
    }
  };

  static AxiomRecord make_axiom_record(const std::monostate &_x);
  static MysteryType extract_axiom_field(const AxiomRecord &r);

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
    AxiomInductive() {}

    explicit AxiomInductive(AxConstr1 _v) : d_v_(std::move(_v)) {}

    explicit AxiomInductive(AxConstr2 _v) : d_v_(std::move(_v)) {}

    AxiomInductive(const AxiomInductive &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    AxiomInductive(AxiomInductive &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) AxiomInductive &
    operator=(const AxiomInductive &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) AxiomInductive &operator=(AxiomInductive &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) AxiomInductive clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<AxConstr1>(_sv.v())) {
        const auto &[d_a0] = std::get<AxConstr1>(_sv.v());
        return AxiomInductive(AxConstr1{d_a0});
      } else {
        const auto &[d_a0] = std::get<AxConstr2>(_sv.v());
        return AxiomInductive(AxConstr2{d_a0});
      }
    }

    // CREATORS
    __attribute__((pure)) static AxiomInductive axconstr1(unsigned int a0) {
      return AxiomInductive(AxConstr1{std::move(a0)});
    }

    __attribute__((pure)) static AxiomInductive axconstr2(MysteryType a0) {
      return AxiomInductive(AxConstr2{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) AxiomInductive *operator->() { return this; }

    __attribute__((pure)) const AxiomInductive *operator->() const {
      return this;
    }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = AxiomInductive(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, MysteryType> F1>
  static T1 AxiomInductive_rect(F0 &&f, F1 &&f0, const AxiomInductive &a) {
    if (std::holds_alternative<typename AxiomInductive::AxConstr1>(a.v())) {
      const auto &[d_a0] = std::get<typename AxiomInductive::AxConstr1>(a.v());
      return f(d_a0);
    } else {
      const auto &[d_a0] = std::get<typename AxiomInductive::AxConstr2>(a.v());
      return f0(d_a0);
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, MysteryType> F1>
  static T1 AxiomInductive_rec(F0 &&f, F1 &&f0, const AxiomInductive &a) {
    if (std::holds_alternative<typename AxiomInductive::AxConstr1>(a.v())) {
      const auto &[d_a0] = std::get<typename AxiomInductive::AxConstr1>(a.v());
      return f(d_a0);
    } else {
      const auto &[d_a0] = std::get<typename AxiomInductive::AxConstr2>(a.v());
      return f0(d_a0);
    }
  }

  static AxiomInductive use_axiom_inductive(const std::monostate &_x);
  static MysteryType axiom_identity(const MysteryType x);
  static MysteryType nested_axiom(const std::monostate &_x);

  template <typename t_A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      t_A d_a0;
      std::unique_ptr<list<t_A>> d_a1;
    };

    using variant_t = std::variant<Nil, Cons>;
    using crane_element_type = t_A;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    list() {}

    explicit list(Nil _v) : d_v_(_v) {}

    explicit list(Cons _v) : d_v_(std::move(_v)) {}

    list(const list<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    list(list<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) list<t_A> &operator=(const list<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) list<t_A> &operator=(list<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) list<t_A> clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Nil>(_sv.v())) {
        return list<t_A>(Nil{});
      } else {
        const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
        return list<t_A>(Cons{
            d_a0, d_a1 ? std::make_unique<AxiomTypes::list<t_A>>(d_a1->clone())
                       : nullptr});
      }
    }

    // CREATORS
    template <typename _U> explicit list(const list<_U> &_other) {
      if (std::holds_alternative<typename list<_U>::Nil>(_other.v())) {
        d_v_ = Nil{};
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<_U>::Cons>(_other.v());
        d_v_ = Cons{t_A(d_a0),
                    d_a1 ? std::make_unique<list<t_A>>(*d_a1) : nullptr};
      }
    }

    __attribute__((pure)) static list<t_A> nil() { return list(Nil{}); }

    __attribute__((pure)) static list<t_A> cons(t_A a0, const list<t_A> &a1) {
      return list(Cons{std::move(a0), std::make_unique<list<t_A>>(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) list<t_A> *operator->() { return this; }

    __attribute__((pure)) const list<t_A> *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = list<t_A>(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1, MapsTo<T1, t_A, list<t_A>, T1> F1>
    T1 list_rec(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename list<t_A>::Nil>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename list<t_A>::Cons>(_sv.v());
        return f0(d_a0, *(d_a1), (*(d_a1)).template list_rec<T1>(f, f0));
      }
    }

    template <typename T1, MapsTo<T1, t_A, list<t_A>, T1> F1>
    T1 list_rect(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename list<t_A>::Nil>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename list<t_A>::Cons>(_sv.v());
        return f0(d_a0, *(d_a1), (*(d_a1)).template list_rect<T1>(f, f0));
      }
    }
  };

  static list<MysteryType> axiom_list(const std::monostate &_x);

  template <typename T1> static T1 poly_axiom(const T1 x) { return x; }

  static MysteryType use_poly_axiom(const std::monostate &_x);
};

#endif // INCLUDED_AXIOM_TYPES
