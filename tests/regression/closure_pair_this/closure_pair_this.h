#ifndef INCLUDED_CLOSURE_PAIR_THIS
#define INCLUDED_CLOSURE_PAIR_THIS

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct ClosurePairThis {
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

    /// BUG HYPOTHESIS: get_fn_pair returns two closures in a pair.
    /// When methodified, both closures capture the raw this pointer.
    /// The pair is custom-extracted as std::make_pair, so the closures
    /// are evaluated and stored while this is still valid.
    /// But after get_fn_pair returns, the temporary tree may be
    /// destroyed — calling either closure is then use-after-free.
    std::pair<std::function<uint64_t(uint64_t)>,
              std::function<uint64_t(uint64_t)>>
    get_fn_pair(uint64_t flag) const {
      tree _self_val = *this;
      if (flag <= 0) {
        return std::make_pair(
            [=](uint64_t x) mutable { return (x + _self_val.tree_sum()); },
            [=](uint64_t x) mutable { return (_self_val.tree_sum() * x); });
      } else {
        uint64_t _x = flag - 1;
        return std::make_pair(
            [=](uint64_t x) mutable { return (_self_val.tree_sum() + x); },
            [](uint64_t x) { return x; });
      }
    }

    uint64_t tree_sum() const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _After_Node: saves [a0, a1], dispatches next recursive call.
      struct _After_Node {
        tree *a0;
        uint64_t a1;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        uint64_t _result;
        uint64_t a1;
      };

      using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified tree_sum: _Enter -> _After_Node -> _Combine_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_After_Node{crane_raw(a0), a1});
            _stack.emplace_back(_Enter{crane_raw(a2)});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{std::move(_result), _f.a1});
          _stack.emplace_back(_Enter{_f.a0});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = ((std::move(_result) + _f.a1) + std::move(_f._result));
        }
      }
      return _result;
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

  struct wrapper {
    // DATA
    tree a0;

    // ACCESSORS
    wrapper clone() const { return {a0}; }

    // CREATORS
    static wrapper wrap(tree a0) { return {std::move(a0)}; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, tree &>
  static T1 wrapper_rect(F0 &&f, const wrapper &w) {
    const auto &[a0] = w;
    return f(a0);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, tree &>
  static T1 wrapper_rec(F0 &&f, const wrapper &w) {
    const auto &[a0] = w;
    return f(a0);
  }

  /// test1: flag=0 on tree with sum=7. fst closure adds, snd multiplies.
  /// (3 + 7) + (7 * 2) = 10 + 14 = 24.
  static inline const uint64_t test1 = []() {
    std::pair<std::function<uint64_t(uint64_t)>,
              std::function<uint64_t(uint64_t)>>
        p = tree::node(tree::leaf(), UINT64_C(7), tree::leaf())
                .get_fn_pair(UINT64_C(0));
    return (p.first(UINT64_C(3)) + p.second(UINT64_C(2)));
  }();
  /// test2: flag=1. fst closure adds sum, snd is identity.
  /// (7 + 4) + 5 = 11 + 5 = 16.
  static inline const uint64_t test2 = []() {
    std::pair<std::function<uint64_t(uint64_t)>,
              std::function<uint64_t(uint64_t)>>
        p = tree::node(tree::leaf(), UINT64_C(7), tree::leaf())
                .get_fn_pair(UINT64_C(1));
    return (p.first(UINT64_C(4)) + p.second(UINT64_C(5)));
  }();
  /// test3: Use both closures after allocating another tree to increase
  /// memory pressure on the freed region.
  static inline const uint64_t test3 = []() {
    std::pair<std::function<uint64_t(uint64_t)>,
              std::function<uint64_t(uint64_t)>>
        p = tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                       UINT64_C(5),
                       tree::node(tree::leaf(), UINT64_C(2), tree::leaf()))
                .get_fn_pair(UINT64_C(0));
    uint64_t noise =
        tree::node(tree::leaf(), UINT64_C(999), tree::leaf()).tree_sum();
    uint64_t a = p.first(noise);
    uint64_t b = std::move(p).second(UINT64_C(1));
    return (a + b);
  }();
};

#endif // INCLUDED_CLOSURE_PAIR_THIS
