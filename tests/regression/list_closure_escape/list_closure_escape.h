#ifndef INCLUDED_LIST_CLOSURE_ESCAPE
#define INCLUDED_LIST_CLOSURE_ESCAPE

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct ListClosureEscape {
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<tree> a0;
      uint64_t a1;
      std::shared_ptr<tree> a2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Leaf _v) : v_(_v) {}

    explicit tree(Node _v) : v_(std::move(_v)) {}

    static tree leaf() { return tree(Leaf{}); }

    static tree node(tree a0, uint64_t a1, tree a2) {
      return tree(Node{std::make_shared<tree>(std::move(a0)), a1,
                       std::make_shared<tree>(std::move(a2))});
    }

    // MANIPULATORS
    ~tree() {
      crane::small_vector<std::shared_ptr<tree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a2) {
            _stack.push_back(std::move(_alt->a2));
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

    uint64_t sum_values(uint64_t x) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return x;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        auto &&_sv0 = *a0;
        if (std::holds_alternative<typename tree::Leaf>(_sv0.v())) {
          return (a1 + x);
        } else {
          const auto &[a00, a10, a20] = std::get<typename tree::Node>(_sv0.v());
          auto &&_sv1 = *a2;
          if (std::holds_alternative<typename tree::Leaf>(_sv1.v())) {
            return (a10 + x);
          } else {
            const auto &[a01, a11, a21] =
                std::get<typename tree::Node>(_sv1.v());
            return (((a10 + a11) + a1) + x);
          }
        }
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, uint64_t &, tree &,
                                     T1 &>
    T1 tree_rec(T1 f, F1 &&f0) const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _After_Node: saves [a0_0, a2, a1, a0_1], dispatches next recursive
      /// call.
      struct _After_Node {
        tree *a0_0;
        tree a2;
        uint64_t a1;
        tree a0_1;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        std::decay_t<T1> _result;
        tree a2;
        uint64_t a1;
        tree a0;
      };

      using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified tree_rec: _Enter -> _After_Node -> _Combine_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_After_Node{crane_raw(a0), *a2, a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a2)});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{
              std::move(_result), std::move(_f.a2), _f.a1, std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = f0(std::move(_f.a0), std::move(_result), _f.a1,
                       std::move(_f.a2), std::move(_f._result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, uint64_t &, tree &,
                                     T1 &>
    T1 tree_rect(T1 f, F1 &&f0) const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _After_Node: saves [a0_0, a2, a1, a0_1], dispatches next recursive
      /// call.
      struct _After_Node {
        tree *a0_0;
        tree a2;
        uint64_t a1;
        tree a0_1;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        std::decay_t<T1> _result;
        tree a2;
        uint64_t a1;
        tree a0;
      };

      using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified tree_rect: _Enter -> _After_Node -> _Combine_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_After_Node{crane_raw(a0), *a2, a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a2)});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{
              std::move(_result), std::move(_f.a2), _f.a1, std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = f0(std::move(_f.a0), std::move(_result), _f.a1,
                       std::move(_f.a2), std::move(_f._result));
        }
      }
      return _result;
    }
  };

  /// A simple list of closures.
  struct fn_list {
    // TYPES
    struct FNil {};

    struct FCons {
      std::function<uint64_t(uint64_t)> a0;
      std::shared_ptr<fn_list> a1;
    };

    using variant_t = std::variant<FNil, FCons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    fn_list() {}

    explicit fn_list(FNil _v) : v_(_v) {}

    explicit fn_list(FCons _v) : v_(std::move(_v)) {}

    static fn_list fnil() { return fn_list(FNil{}); }

    static fn_list fcons(std::function<uint64_t(uint64_t)> a0, fn_list a1) {
      return fn_list(
          FCons{std::move(a0), std::make_shared<fn_list>(std::move(a1))});
    }

    // MANIPULATORS
    ~fn_list() {
      crane::small_vector<std::shared_ptr<fn_list>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<FCons>(&_v)) {
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

    fn_list(const fn_list &) = default;
    fn_list &operator=(const fn_list &) = default;
    fn_list(fn_list &&) noexcept = default;
    fn_list &operator=(fn_list &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t apply_first(uint64_t x) const {
      if (std::holds_alternative<typename fn_list::FNil>(this->v())) {
        return x;
      } else {
        const auto &[a0, a1] = std::get<typename fn_list::FCons>(this->v());
        return a0(x);
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<
          T1, F1 &, std::function<uint64_t(uint64_t)> &, fn_list &, T1 &>
    T1 fn_list_rec(T1 f, F1 &&f0) const {
      const fn_list *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const fn_list *_self;
      };

      /// _Resume_FCons: saves [a1, a0], resumes after recursive call with
      /// _result.
      struct _Resume_FCons {
        fn_list a1;
        std::function<uint64_t(uint64_t)> a0;
      };

      using _Frame = std::variant<_Enter, _Resume_FCons>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified fn_list_rec: _Enter -> _Resume_FCons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const fn_list *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename fn_list::FNil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] = std::get<typename fn_list::FCons>(_sv.v());
            _stack.emplace_back(_Resume_FCons{*a1, std::move(a0)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_Resume_FCons>(_frame));
          _result = f0(std::move(_f.a0), std::move(_f.a1), std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<
          T1, F1 &, std::function<uint64_t(uint64_t)> &, fn_list &, T1 &>
    T1 fn_list_rect(T1 f, F1 &&f0) const {
      const fn_list *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const fn_list *_self;
      };

      /// _Resume_FCons: saves [a1, a0], resumes after recursive call with
      /// _result.
      struct _Resume_FCons {
        fn_list a1;
        std::function<uint64_t(uint64_t)> a0;
      };

      using _Frame = std::variant<_Enter, _Resume_FCons>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified fn_list_rect: _Enter -> _Resume_FCons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const fn_list *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename fn_list::FNil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] = std::get<typename fn_list::FCons>(_sv.v());
            _stack.emplace_back(_Resume_FCons{*a1, std::move(a0)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_Resume_FCons>(_frame));
          _result = f0(std::move(_f.a0), std::move(_f.a1), std::move(_result));
        }
      }
      return _result;
    }
  };

  /// BUG: partial applications stored in a custom list via FCons.
  /// Each lambda for (sum_values t_i) captures t_i by &.
  /// When build_fns returns, t1 and t2 are destroyed.
  static fn_list build_fns(tree t1, tree t2);
  static inline const uint64_t bug_list_clobber = []() {
    tree t1 = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                         UINT64_C(20),
                         tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
    tree t2 = tree::node(tree::node(tree::leaf(), UINT64_C(77), tree::leaf()),
                         UINT64_C(88),
                         tree::node(tree::leaf(), UINT64_C(99), tree::leaf()));
    fn_list fns = build_fns(std::move(t1), std::move(t2));
    return std::move(fns).apply_first(UINT64_C(0));
  }();
};

#endif // INCLUDED_LIST_CLOSURE_ESCAPE
