#ifndef INCLUDED_NESTED_INDUCTIVE_NO_DRAIN
#define INCLUDED_NESTED_INDUCTIVE_NO_DRAIN

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
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
        this->v_ = Cons{[&]() -> A {
                          if constexpr (std::is_same_v<_U, std::any>) {
                            return crane_any_cast<A>(a0);
                          } else {
                            return A(a0);
                          }
                        }(),
                        (a1 ? std::make_shared<lst<A>>(*a1) : nullptr)};
      }
    }

    static lst<A> nil() { return lst<A>(Nil{}); }

    static lst<A> cons(A a0, lst<A> a1) {
      return lst<A>(
          Cons{std::move(a0), std::make_shared<lst<A>>(std::move(a1))});
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
          std::atomic_thread_fence(std::memory_order_acquire);
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
      const lst<A> *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const lst<A> *_self;
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
          const lst<A> *_self = _f._self;
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
      const lst<A> *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const lst<A> *_self;
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
          const lst<A> *_self = _f._self;
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
    ~tree() {
      crane::small_vector<std::shared_ptr<tree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            auto _lp = _alt->a1.get();
            while (std::holds_alternative<
                   typename NestedInductiveNoDrain::lst<tree>::Cons>(
                _lp->v())) {
              auto &_lc =
                  std::get<typename NestedInductiveNoDrain::lst<tree>::Cons>(
                      _lp->v_mut());
              _stack.push_back(std::make_shared<tree>(std::move(_lc.a0)));
              if (_lc.a1 && _lc.a1.use_count() == 1) {
                std::atomic_thread_fence(std::memory_order_acquire);
                _lp = _lc.a1.get();
              } else {
                break;
              }
            }
            _alt->a1.reset();
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

    tree(const tree &) = default;
    tree &operator=(const tree &) = default;
    tree(tree &&) noexcept = default;
    tree &operator=(tree &&) noexcept = default;

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
      tree _self_store;
      const tree *_loop_self = this;
      uint64_t _loop_n = std::move(n);
      while (true) {
        if (_loop_n <= 0) {
          return std::move(*_loop_self);
        } else {
          uint64_t m = _loop_n - 1;
          _self_store =
              tree::node(_loop_n, lst<tree>::cons(std::move(*_loop_self),
                                                  lst<tree>::nil()));
          _loop_self = &_self_store;
          _loop_n = m;
        }
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
