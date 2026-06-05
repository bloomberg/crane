#ifndef INCLUDED_AXIOM_TYPES
#define INCLUDED_AXIOM_TYPES

#include <any>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct AxiomTypes {
  using MysteryType = std::any /* AXIOM TO BE REALIZED */;
  static MysteryType mystery_value();
  static MysteryType mystery_function(MysteryType _x0);
  static MysteryType use_axiom(std::monostate _x);

  struct AxiomRecord {
    uint64_t normal_field;
    MysteryType axiom_field;
  };

  static AxiomRecord make_axiom_record(std::monostate _x);
  static MysteryType extract_axiom_field(const AxiomRecord &r);

  struct AxiomInductive {
    // TYPES
    struct AxConstr1 {
      uint64_t a0;
    };

    struct AxConstr2 {
      MysteryType a0;
    };

    using variant_t = std::variant<AxConstr1, AxConstr2>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    AxiomInductive() {}

    explicit AxiomInductive(AxConstr1 _v) : v_(std::move(_v)) {}

    explicit AxiomInductive(AxConstr2 _v) : v_(std::move(_v)) {}

    static AxiomInductive axconstr1(uint64_t a0) {
      return AxiomInductive(AxConstr1{a0});
    }

    static AxiomInductive axconstr2(MysteryType a0) {
      return AxiomInductive(AxConstr2{std::move(a0)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, MysteryType &>
  static T1 AxiomInductive_rect(F0 &&f, F1 &&f0, const AxiomInductive &a) {
    if (std::holds_alternative<typename AxiomInductive::AxConstr1>(a.v())) {
      const auto &[a0] = std::get<typename AxiomInductive::AxConstr1>(a.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename AxiomInductive::AxConstr2>(a.v());
      return f0(a0);
    }
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, MysteryType &>
  static T1 AxiomInductive_rec(F0 &&f, F1 &&f0, const AxiomInductive &a) {
    if (std::holds_alternative<typename AxiomInductive::AxConstr1>(a.v())) {
      const auto &[a0] = std::get<typename AxiomInductive::AxConstr1>(a.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename AxiomInductive::AxConstr2>(a.v());
      return f0(a0);
    }
  }

  static AxiomInductive use_axiom_inductive(std::monostate _x);
  static MysteryType axiom_identity(MysteryType x);
  static MysteryType nested_axiom(std::monostate _x);

  template <typename A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      A a0;
      std::shared_ptr<list<A>> a1;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    list() {}

    explicit list(Nil _v) : v_(_v) {}

    explicit list(Cons _v) : v_(std::move(_v)) {}

    template <typename _U> explicit list(const list<_U> &_other) {
      if (std::holds_alternative<typename list<_U>::Nil>(_other.v())) {
        this->v_ = Nil{};
      } else {
        const auto &[a0, a1] = std::get<typename list<_U>::Cons>(_other.v());
        this->v_ = Cons{
            [&]() -> A {
              if constexpr (std::is_same_v<_U, std::any>) {
                if (a0.type() == typeid(A))
                  return std::any_cast<A>(a0);
                if constexpr (requires {
                                typename A::first_type;
                                typename A::second_type;
                              }) {
                  const auto &[_k, _v] =
                      std::any_cast<std::pair<std::any, std::any>>(a0);
                  return A{
                      [&]() -> typename A::first_type {
                        if constexpr (std::is_same_v<typename A::first_type,
                                                     std::any>)
                          return _k;
                        else
                          return std::any_cast<typename A::first_type>(_k);
                      }(),
                      [&]() -> typename A::second_type {
                        if constexpr (std::is_same_v<typename A::second_type,
                                                     std::any>)
                          return _v;
                        else
                          return std::any_cast<typename A::second_type>(_v);
                      }()};
                }
                return std::any_cast<A>(a0);
              } else
                return A(a0);
            }(),
            a1 ? std::make_shared<list<A>>(*a1) : nullptr};
      }
    }

    static list<A> nil() { return list(Nil{}); }

    static list<A> cons(A a0, list<A> a1) {
      return list(
          Cons{std::move(a0), std::make_shared<list<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~list() {
      std::vector<std::shared_ptr<list<A>>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Cons>(&_v)) {
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          _drain(_cur->v_mut());
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, list<A> &, T1 &>
    T1 list_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename list<A>::Nil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] = std::get<typename list<A>::Cons>(this->v());
        return f0(a0, *a1, a1->template list_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, list<A> &, T1 &>
    T1 list_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename list<A>::Nil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] = std::get<typename list<A>::Cons>(this->v());
        return f0(a0, *a1, a1->template list_rect<T1>(f, f0));
      }
    }
  };

  static list<MysteryType> axiom_list(std::monostate _x);

  template <typename T1> static T1 poly_axiom(T1 x) { return x; }

  static MysteryType use_poly_axiom(std::monostate _x);
};

#endif // INCLUDED_AXIOM_TYPES
