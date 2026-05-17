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

    // ACCESSORS
    AxiomRecord clone() const {
      return AxiomRecord{(*this).normal_field, (*this).axiom_field};
    }
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

    AxiomInductive(const AxiomInductive &_other)
        : v_(std::move(_other.clone().v_)) {}

    AxiomInductive(AxiomInductive &&_other) noexcept
        : v_(std::move(_other.v_)) {}

    AxiomInductive &operator=(const AxiomInductive &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    AxiomInductive &operator=(AxiomInductive &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    AxiomInductive clone() const {
      if (std::holds_alternative<AxConstr1>(this->v())) {
        const auto &[a0] = std::get<AxConstr1>(this->v());
        return AxiomInductive(AxConstr1{a0});
      } else {
        const auto &[a0] = std::get<AxConstr2>(this->v());
        return AxiomInductive(AxConstr2{a0});
      }
    }

    // CREATORS
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
      std::unique_ptr<list<A>> a1;
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

    list(const list<A> &_other) : v_(std::move(_other.clone().v_)) {}

    list(list<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

    list<A> &operator=(const list<A> &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    list<A> &operator=(list<A> &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    list<A> clone() const {
      list<A> _out{};

      struct _CloneFrame {
        const list<A> *_src;
        list<A> *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const list<A> *_src = _frame._src;
        list<A> *_dst = _frame._dst;
        if (std::holds_alternative<Nil>(_src->v())) {
          _dst->v_ = Nil{};
        } else {
          const auto &_alt = std::get<Cons>(_src->v());
          _dst->v_ =
              Cons{_alt.a0, _alt.a1 ? std::make_unique<list<A>>() : nullptr};
          auto &_dst_alt = std::get<Cons>(_dst->v_);
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    template <typename _U> explicit list(const list<_U> &_other) {
      if (std::holds_alternative<typename list<_U>::Nil>(_other.v())) {
        this->v_ = Nil{};
      } else {
        const auto &[a0, a1] = std::get<typename list<_U>::Cons>(_other.v());
        this->v_ = Cons{A(a0), a1 ? std::make_unique<list<A>>(*a1) : nullptr};
      }
    }

    static list<A> nil() { return list(Nil{}); }

    static list<A> cons(A a0, list<A> a1) {
      return list(
          Cons{std::move(a0), std::make_unique<list<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~list() {
      std::vector<std::unique_ptr<list<A>>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](list<A> &_node) {
        if (std::holds_alternative<Cons>(_node.v_)) {
          auto &_alt = std::get<Cons>(_node.v_);
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
          }
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node) {
          _drain(*_node);
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
        return f0(a0, *a1, (*a1).template list_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, list<A> &, T1 &>
    T1 list_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename list<A>::Nil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] = std::get<typename list<A>::Cons>(this->v());
        return f0(a0, *a1, (*a1).template list_rect<T1>(f, f0));
      }
    }
  };

  static list<MysteryType> axiom_list(std::monostate _x);

  template <typename T1> static T1 poly_axiom(T1 x) { return x; }

  static MysteryType use_poly_axiom(std::monostate _x);
};

#endif // INCLUDED_AXIOM_TYPES
