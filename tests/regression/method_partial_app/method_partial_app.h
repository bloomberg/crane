#ifndef INCLUDED_METHOD_PARTIAL_APP
#define INCLUDED_METHOD_PARTIAL_APP

#include "crane_fn.h"
#include "fn.h"
#include "small_vector.h"
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct MethodPartialApp {
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
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a2 && _alt->a2.use_count() == 1) {
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

    /// add_to_sum: methodified on first arg (tree).
    /// Takes a tree and a nat, returns the tree's sum plus the nat.
    uint64_t add_to_sum(uint64_t x) const { return (this->tree_sum() + x); }

    uint64_t tree_sum() const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _Cont_Node: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Node {
        uint64_t a1;
        std::shared_ptr<tree> a2;
      };

      /// _Cont_Node_1: saves [_tmp2, a1], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Node_1 {
        uint64_t _tmp2;
        uint64_t a1;
      };

      using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified tree_sum: _Enter -> _Cont_Node -> _Cont_Node_1.
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
            _stack.emplace_back(_Cont_Node{a1, a2});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_Cont_Node>(_frame)) {
          auto _f = std::move(std::get<_Cont_Node>(_frame));
          uint64_t a1 = _f.a1;
          std::shared_ptr<tree> a2 = std::move(_f.a2);
          _stack.emplace_back(_Cont_Node_1{std::move(_result), a1});
          _stack.emplace_back(_Enter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<_Cont_Node_1>(_frame));
          uint64_t a1 = _f.a1;
          _result = ((_f._tmp2 + a1) + std::move(_result));
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

      /// _Cont_Node: saves [a0, a1, a2], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Node {
        std::shared_ptr<tree> a0;
        uint64_t a1;
        std::shared_ptr<tree> a2;
      };

      /// _Cont_Node_1: saves [_tmp2, a0, a1, a2], resumes after recursive call,
      /// then processes rest.
      struct _Cont_Node_1 {
        T1 _tmp2;
        std::shared_ptr<tree> a0;
        uint64_t a1;
        std::shared_ptr<tree> a2;
      };

      using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified tree_rec: _Enter -> _Cont_Node -> _Cont_Node_1.
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
            _stack.emplace_back(_Cont_Node{a0, a1, a2});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_Cont_Node>(_frame)) {
          auto _f = std::move(std::get<_Cont_Node>(_frame));
          std::shared_ptr<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          std::shared_ptr<tree> a2 = std::move(_f.a2);
          _stack.emplace_back(
              _Cont_Node_1{std::move(_result), std::move(a0), a1, a2});
          _stack.emplace_back(_Enter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<_Cont_Node_1>(_frame));
          std::shared_ptr<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          std::shared_ptr<tree> a2 = std::move(_f.a2);
          _result = f0(*a0, std::move(_f._tmp2), a1, *a2, std::move(_result));
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

      /// _Cont_Node: saves [a0, a1, a2], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Node {
        std::shared_ptr<tree> a0;
        uint64_t a1;
        std::shared_ptr<tree> a2;
      };

      /// _Cont_Node_1: saves [_tmp2, a0, a1, a2], resumes after recursive call,
      /// then processes rest.
      struct _Cont_Node_1 {
        T1 _tmp2;
        std::shared_ptr<tree> a0;
        uint64_t a1;
        std::shared_ptr<tree> a2;
      };

      using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified tree_rect: _Enter -> _Cont_Node -> _Cont_Node_1.
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
            _stack.emplace_back(_Cont_Node{a0, a1, a2});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_Cont_Node>(_frame)) {
          auto _f = std::move(std::get<_Cont_Node>(_frame));
          std::shared_ptr<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          std::shared_ptr<tree> a2 = std::move(_f.a2);
          _stack.emplace_back(
              _Cont_Node_1{std::move(_result), std::move(a0), a1, a2});
          _stack.emplace_back(_Enter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<_Cont_Node_1>(_frame));
          std::shared_ptr<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          std::shared_ptr<tree> a2 = std::move(_f.a2);
          _result = f0(*a0, std::move(_f._tmp2), a1, *a2, std::move(_result));
        }
      }
      return _result;
    }
  };

  /// Direct partial app stored in let, called twice.
  static inline const uint64_t method_partial_bug = []() {
    return []() {
      tree t = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                          UINT64_C(20),
                          tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
      crane::fn<uint64_t(uint64_t)> f = [=](uint64_t _x0) -> uint64_t {
        return std::move(t).add_to_sum(_x0);
      };
      return (f(UINT64_C(5)) + f(UINT64_C(10)));
    }();
  }();

  /// Partial app stored in a constructor.
  struct box {
    // DATA
    crane::fn<uint64_t(uint64_t)> a0;

    // ACCESSORS
    box clone() const { return {a0}; }

    // CREATORS
    static box box0(crane::fn<uint64_t(uint64_t)> a0) {
      return {std::move(a0)};
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, crane::fn<uint64_t(uint64_t)> &>
    T1 box_rec(F0 &&f) const {
      const auto &[a0] = *this;
      return f(a0);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, crane::fn<uint64_t(uint64_t)> &>
    T1 box_rect(F0 &&f) const {
      const auto &[a0] = *this;
      return f(a0);
    }
  };

  static inline const uint64_t method_partial_box = []() {
    return []() {
      tree t = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                          UINT64_C(20),
                          tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
      box b = box::box0([=](uint64_t _x0) -> uint64_t {
        return std::move(t).add_to_sum(_x0);
      });
      auto &[a0] = b;
      return (a0(UINT64_C(5)) + a0(UINT64_C(10)));
    }();
  }();
  /// Two partial apps from different trees.
  static inline const uint64_t method_partial_two = []() {
    return []() {
      tree t1 = tree::node(tree::leaf(), UINT64_C(10), tree::leaf());
      tree t2 = tree::node(tree::leaf(), UINT64_C(20), tree::leaf());
      crane::fn<uint64_t(uint64_t)> f1 = [&](uint64_t _x0) -> uint64_t {
        return std::move(t1).add_to_sum(_x0);
      };
      crane::fn<uint64_t(uint64_t)> f2 = [&](uint64_t _x0) -> uint64_t {
        return std::move(t2).add_to_sum(_x0);
      };
      return (f1(UINT64_C(0)) + f2(UINT64_C(0)));
    }();
  }();
};

#endif // INCLUDED_METHOD_PARTIAL_APP
