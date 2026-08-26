#ifndef INCLUDED_MUTUAL_LOOPIFY_ACC
#define INCLUDED_MUTUAL_LOOPIFY_ACC

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct MutualLoopifyAcc {
  struct tree;
  struct forest;

  struct tree {
    // TYPES
    struct Leaf {
      uint64_t a0;
    };

    struct Node {
      std::shared_ptr<forest> a0;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Leaf _v) : v_(std::move(_v)) {}

    explicit tree(Node _v) : v_(std::move(_v)) {}

    static tree leaf(uint64_t a0) { return tree(Leaf{a0}); }

    static tree node(forest a0) {
      return tree(Node{std::make_shared<forest>(std::move(a0))});
    }

    // MANIPULATORS
    ~tree() {
      crane::small_vector<std::any> _stack = {};
      auto _drain_self = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
        }
      };
      _drain_self(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (auto *_sp = std::any_cast<std::shared_ptr<tree>>(&_cur)) {
          if (*_sp && (*_sp).use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            _drain_self((*_sp)->v_mut());
          }
        } else {
          if (auto *_sp = std::any_cast<std::shared_ptr<forest>>(&_cur)) {
            if (*_sp && (*_sp).use_count() == 1) {
              auto &_pv = (*_sp)->v_mut();
              if (auto *_alt = std::get_if<typename forest::Fcons>(&_pv)) {
                if (_alt->a0) {
                  _stack.push_back(std::move(_alt->a0));
                }
                if (_alt->a1) {
                  _stack.push_back(std::move(_alt->a1));
                }
              }
            }
          }
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
  };

  struct forest {
    // TYPES
    struct Fnil {};

    struct Fcons {
      std::shared_ptr<tree> a0;
      std::shared_ptr<forest> a1;
    };

    using variant_t = std::variant<Fnil, Fcons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    forest() {}

    explicit forest(Fnil _v) : v_(_v) {}

    explicit forest(Fcons _v) : v_(std::move(_v)) {}

    static forest fnil() { return forest(Fnil{}); }

    static forest fcons(tree a0, forest a1) {
      return forest(Fcons{std::make_shared<tree>(std::move(a0)),
                          std::make_shared<forest>(std::move(a1))});
    }

    // MANIPULATORS
    ~forest() {
      crane::small_vector<std::any> _stack = {};
      auto _drain_self = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Fcons>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
      };
      _drain_self(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (auto *_sp = std::any_cast<std::shared_ptr<forest>>(&_cur)) {
          if (*_sp && (*_sp).use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            _drain_self((*_sp)->v_mut());
          }
        } else {
          if (auto *_sp = std::any_cast<std::shared_ptr<tree>>(&_cur)) {
            if (*_sp && (*_sp).use_count() == 1) {
              auto &_pv = (*_sp)->v_mut();
              if (auto *_alt = std::get_if<typename tree::Node>(&_pv)) {
                if (_alt->a0) {
                  _stack.push_back(std::move(_alt->a0));
                }
              }
            }
          }
        }
      }
    }

    forest(const forest &) = default;
    forest &operator=(const forest &) = default;
    forest(forest &&) noexcept = default;
    forest &operator=(forest &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, forest &>
  static T1 tree_rect(F0 &&f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      const auto &[a0] = std::get<typename tree::Leaf>(t.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename tree::Node>(t.v());
      return f0(*a0);
    }
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, forest &>
  static T1 tree_rec(F0 &&f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      const auto &[a0] = std::get<typename tree::Leaf>(t.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename tree::Node>(t.v());
      return f0(*a0);
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, tree &, forest &, T1 &>
  static T1
  forest_rect(T1 f, F1 &&f0,
              const forest &f1) { /// _Enter: captures varying parameters for
                                  /// each recursive call.

    struct _Enter {
      const forest *f1;
    };

    /// _Resume_Fcons: saves [a1, a0], resumes after recursive call with
    /// _result.
    struct _Resume_Fcons {
      forest a1;
      tree a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Fcons>;
    T1 _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&f1});
    /// Loopified forest_rect: _Enter -> _Resume_Fcons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const forest &f1 = *_f.f1;
        if (std::holds_alternative<typename forest::Fnil>(f1.v())) {
          _result = f;
        } else {
          const auto &[a0, a1] = std::get<typename forest::Fcons>(f1.v());
          _stack.emplace_back(_Resume_Fcons{*a1, *a0});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Fcons>(_frame));
        _result = f0(std::move(_f.a0), std::move(_f.a1), std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, tree &, forest &, T1 &>
  static T1
  forest_rec(T1 f, F1 &&f0,
             const forest &f1) { /// _Enter: captures varying parameters for
                                 /// each recursive call.

    struct _Enter {
      const forest *f1;
    };

    /// _Resume_Fcons: saves [a1, a0], resumes after recursive call with
    /// _result.
    struct _Resume_Fcons {
      forest a1;
      tree a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Fcons>;
    T1 _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&f1});
    /// Loopified forest_rec: _Enter -> _Resume_Fcons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const forest &f1 = *_f.f1;
        if (std::holds_alternative<typename forest::Fnil>(f1.v())) {
          _result = f;
        } else {
          const auto &[a0, a1] = std::get<typename forest::Fcons>(f1.v());
          _stack.emplace_back(_Resume_Fcons{*a1, *a0});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Fcons>(_frame));
        _result = f0(std::move(_f.a0), std::move(_f.a1), std::move(_result));
      }
    }
    return _result;
  }

  static uint64_t tsum(uint64_t acc, const tree &t);
  static uint64_t fsum(uint64_t acc, const forest &f);
  static tree chain(uint64_t n, tree acc);
  static uint64_t go(uint64_t n);
};

#endif // INCLUDED_MUTUAL_LOOPIFY_ACC
