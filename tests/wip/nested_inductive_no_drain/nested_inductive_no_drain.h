#ifndef INCLUDED_NESTED_INDUCTIVE_NO_DRAIN
#define INCLUDED_NESTED_INDUCTIVE_NO_DRAIN

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct NestedInductiveNoDrain {
  template <typename A> struct lst {
    // TYPES
    struct Nil {};

    struct Cons {
      A a0;
      std::shared_ptr<lst<A>> a1;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    lst() {}

    explicit lst(Nil _v) : v_(_v) {}

    explicit lst(Cons _v) : v_(std::move(_v)) {}

    template <typename _U> lst(const lst<_U> &_other) {
      if (std::holds_alternative<typename lst<_U>::Nil>(_other.v())) {
        this->v_ = Nil{};
      } else {
        const auto &[a0, a1] = std::get<typename lst<_U>::Cons>(_other.v());
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
            a1 ? std::make_shared<lst<A>>(*a1) : nullptr};
      }
    }

    static lst<A> nil() { return lst(Nil{}); }

    static lst<A> cons(A a0, lst<A> a1) {
      return lst(Cons{std::move(a0), std::make_shared<lst<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~lst() {
      crane::small_vector<std::shared_ptr<lst<A>>> _stack = {};
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

    lst(const lst &) = default;
    lst &operator=(const lst &) = default;
    lst(lst &&) noexcept = default;
    lst &operator=(lst &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, lst<A> &, T1 &>
    T1 lst_rec(T1 f, F1 &&f0) const {
      const lst *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const lst *_self;
      };

      /// _Resume_Cons: saves [a1, a0], resumes after recursive call with
      /// _result.
      struct _Resume_Cons {
        lst<A> a1;
        std::decay_t<A> a0;
      };

      using _Frame = std::variant<_Enter, _Resume_Cons>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified lst_rec: _Enter -> _Resume_Cons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const lst *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename lst<A>::Nil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] = std::get<typename lst<A>::Cons>(_sv.v());
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
      requires std::is_invocable_r_v<T1, F1 &, A &, lst<A> &, T1 &>
    T1 lst_rect(T1 f, F1 &&f0) const {
      const lst *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const lst *_self;
      };

      /// _Resume_Cons: saves [a1, a0], resumes after recursive call with
      /// _result.
      struct _Resume_Cons {
        lst<A> a1;
        std::decay_t<A> a0;
      };

      using _Frame = std::variant<_Enter, _Resume_Cons>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified lst_rect: _Enter -> _Resume_Cons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const lst *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename lst<A>::Nil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] = std::get<typename lst<A>::Cons>(_sv.v());
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

  struct tree {
    // TYPES
    struct Node {
      uint64_t a0;
      std::shared_ptr<lst<tree>> a1;
    };

    using variant_t = std::variant<Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Node _v) : v_(std::move(_v)) {}

    static tree node(uint64_t a0, lst<tree> a1) {
      return tree(Node{a0, std::make_shared<lst<tree>>(std::move(a1))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t tsum() const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      using _Frame = std::variant<_Enter>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified tsum: _Enter.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        auto _f = std::move(std::get<_Enter>(_frame));
        const tree *_self = _f._self;
        auto &&_sv = *_self;
        const auto &[a0, a1] = std::get<typename tree::Node>(_sv.v());
        auto go0_impl = [](auto &_self_go0, const lst<tree> &m) -> uint64_t {
          if (std::holds_alternative<typename lst<tree>::Nil>(m.v())) {
            return UINT64_C(0);
          } else {
            const auto &[a2, a3] = std::get<typename lst<tree>::Cons>(m.v());
            return (a2.tsum() + _self_go0(_self_go0, *a3));
          }
        };
        auto go0 = [&](const lst<tree> &m) -> uint64_t {
          return go0_impl(go0_impl, m);
        };
        _result = (a0 + go0(*a1));
      }
      return _result;
    }

    tree spine(uint64_t n) const {
      if (n <= 0) {
        return std::move(*this);
      } else {
        uint64_t m = n - 1;
        return tree::node(n,
                          lst<tree>::cons(std::move(*this), lst<tree>::nil()))
            .spine(m);
      }
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &, lst<tree> &>
    T1 tree_rec(F0 &&f) const {
      const auto &[a0, a1] = std::get<typename tree::Node>(this->v());
      return f(a0, *a1);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &, lst<tree> &>
    T1 tree_rect(F0 &&f) const {
      const auto &[a0, a1] = std::get<typename tree::Node>(this->v());
      return f(a0, *a1);
    }
  };

  static uint64_t go(uint64_t n);
};

#endif // INCLUDED_NESTED_INDUCTIVE_NO_DRAIN
