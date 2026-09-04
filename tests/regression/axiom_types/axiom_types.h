#ifndef INCLUDED_AXIOM_TYPES
#define INCLUDED_AXIOM_TYPES

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

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
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &>
  static T1 AxiomInductive_rect(F0 &&f, F1 &&f0, const AxiomInductive &a) {
    if (std::holds_alternative<typename AxiomInductive::AxConstr1>(a.v())) {
      const auto &[a0] = std::get<typename AxiomInductive::AxConstr1>(a.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename AxiomInductive::AxConstr2>(a.v());
      return crane_call_erased(f0, a0);
    }
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &>
  static T1 AxiomInductive_rec(F0 &&f, F1 &&f0, const AxiomInductive &a) {
    if (std::holds_alternative<typename AxiomInductive::AxConstr1>(a.v())) {
      const auto &[a0] = std::get<typename AxiomInductive::AxConstr1>(a.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename AxiomInductive::AxConstr2>(a.v());
      return crane_call_erased(f0, a0);
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

    template <typename _U> list(const list<_U> &_other) {
      if (std::holds_alternative<typename list<_U>::Nil>(_other.v())) {
        this->v_ = Nil{};
      } else {
        const auto &[a0, a1] = std::get<typename list<_U>::Cons>(_other.v());
        this->v_ = Cons{[&]() -> A {
                          if constexpr (std::is_same_v<_U, std::any>)
                            return crane_any_cast<A>(a0);
                          else
                            return A(a0);
                        }(),
                        (a1 ? std::make_shared<list<A>>(*a1) : nullptr)};
      }
    }

    static list<A> nil() { return list<A>(Nil{}); }

    static list<A> cons(A a0, list<A> a1) {
      return list<A>(
          Cons{std::move(a0), std::make_shared<list<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~list() {
      crane::small_vector<std::shared_ptr<list<A>>> _stack = {};
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
          std::atomic_thread_fence(std::memory_order_acquire);
          _drain(_cur->v_mut());
        }
      }
    }

    list(const list &) = default;
    list &operator=(const list &) = default;
    list(list &&) noexcept = default;
    list &operator=(list &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, list<A> &, T1 &>
    T1 list_rec(T1 f, F1 &&f0) const {
      const list<A> *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const list<A> *_self;
      };

      /// _Resume_Cons: saves [a1, a0], resumes after recursive call with
      /// _result.
      struct _Resume_Cons {
        list<A> a1;
        std::decay_t<A> a0;
      };

      using _Frame = std::variant<_Enter, _Resume_Cons>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified list_rec: _Enter -> _Resume_Cons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const list<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename list<A>::Nil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] = std::get<typename list<A>::Cons>(_sv.v());
            _stack.emplace_back(_Resume_Cons{*a1, a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_Resume_Cons>(_frame));
          _result = f0(std::move(_f.a0), std::move(_f.a1), std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, list<A> &, T1 &>
    T1 list_rect(T1 f, F1 &&f0) const {
      const list<A> *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const list<A> *_self;
      };

      /// _Resume_Cons: saves [a1, a0], resumes after recursive call with
      /// _result.
      struct _Resume_Cons {
        list<A> a1;
        std::decay_t<A> a0;
      };

      using _Frame = std::variant<_Enter, _Resume_Cons>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified list_rect: _Enter -> _Resume_Cons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const list<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename list<A>::Nil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] = std::get<typename list<A>::Cons>(_sv.v());
            _stack.emplace_back(_Resume_Cons{*a1, a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_Resume_Cons>(_frame));
          _result = f0(std::move(_f.a0), std::move(_f.a1), std::move(_result));
        }
      }
      return _result;
    }
  };

  static list<MysteryType> axiom_list(std::monostate _x);

  template <typename T1> static T1 poly_axiom(T1 x) { return x; }

  static MysteryType use_poly_axiom(std::monostate _x);
};

#endif // INCLUDED_AXIOM_TYPES
