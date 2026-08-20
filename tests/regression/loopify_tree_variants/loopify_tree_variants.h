#ifndef INCLUDED_LOOPIFY_TREE_VARIANTS
#define INCLUDED_LOOPIFY_TREE_VARIANTS

#include "crane_fn.h"
#include "small_vector.h"
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct LoopifyTreeVariants {
  struct ternary {
    // TYPES
    struct TLeaf {};

    struct TNode {
      std::shared_ptr<ternary> a0;
      uint64_t a1;
      std::shared_ptr<ternary> a2;
      std::shared_ptr<ternary> a3;
    };

    using variant_t = std::variant<TLeaf, TNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    ternary() {}

    explicit ternary(TLeaf _v) : v_(_v) {}

    explicit ternary(TNode _v) : v_(std::move(_v)) {}

    static ternary tleaf() { return ternary(TLeaf{}); }

    static ternary tnode(ternary a0, uint64_t a1, ternary a2, ternary a3) {
      return ternary(TNode{std::make_shared<ternary>(std::move(a0)), a1,
                           std::make_shared<ternary>(std::move(a2)),
                           std::make_shared<ternary>(std::move(a3))});
    }

    // MANIPULATORS
    ~ternary() {
      crane::small_vector<std::shared_ptr<ternary>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<TNode>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a2) {
            _stack.push_back(std::move(_alt->a2));
          }
          if (_alt->a3) {
            _stack.push_back(std::move(_alt->a3));
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

    ternary(const ternary &) = default;
    ternary &operator=(const ternary &) = default;
    ternary(ternary &&) noexcept = default;
    ternary &operator=(ternary &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t ternary_count() const {
      const ternary *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const ternary *_self;
      };

      /// _After_TNode: saves [a2, a0, _s2], dispatches next recursive call.
      struct _After_TNode {
        const ternary *a2;
        const ternary *a0;
        std::decay_t<decltype(UINT64_C(1))> _s2;
      };

      /// _After_TNode_1: saves [_result, a0, _s2], dispatches next recursive
      /// call.
      struct _After_TNode_1 {
        uint64_t _result;
        const ternary *a0;
        std::decay_t<decltype(UINT64_C(1))> _s2;
      };

      /// _Combine_TNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_TNode {
        uint64_t _result_0;
        uint64_t _result_1;
        std::decay_t<decltype(UINT64_C(1))> _s2;
      };

      using _Frame =
          std::variant<_Enter, _After_TNode, _After_TNode_1, _Combine_TNode>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified ternary_count: _Enter -> _After_TNode -> _After_TNode_1 ->
      /// _Combine_TNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const ternary *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ternary::TLeaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename ternary::TNode>(_sv.v());
            _stack.emplace_back(
                _After_TNode{crane_raw(a2), crane_raw(a0), UINT64_C(1)});
            _stack.emplace_back(_Enter{crane_raw(a3)});
          }
        } else if (std::holds_alternative<_After_TNode>(_frame)) {
          auto _f = std::move(std::get<_After_TNode>(_frame));
          _stack.emplace_back(
              _After_TNode_1{std::move(_result), _f.a0, _f._s2});
          _stack.emplace_back(_Enter{_f.a2});
        } else if (std::holds_alternative<_After_TNode_1>(_frame)) {
          auto _f = std::move(std::get<_After_TNode_1>(_frame));
          _stack.emplace_back(
              _Combine_TNode{_f._result, std::move(_result), _f._s2});
          _stack.emplace_back(_Enter{_f.a0});
        } else {
          auto _f = std::move(std::get<_Combine_TNode>(_frame));
          _result =
              (((_f._s2 + std::move(_result)) + _f._result_1) + _f._result_0);
        }
      }
      return _result;
    }

    uint64_t ternary_sum() const {
      const ternary *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const ternary *_self;
      };

      /// _After_TNode: saves [a2, a0, a1], dispatches next recursive call.
      struct _After_TNode {
        const ternary *a2;
        const ternary *a0;
        uint64_t a1;
      };

      /// _After_TNode_1: saves [_result, a0, a1], dispatches next recursive
      /// call.
      struct _After_TNode_1 {
        uint64_t _result;
        const ternary *a0;
        uint64_t a1;
      };

      /// _Combine_TNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_TNode {
        uint64_t _result_0;
        uint64_t _result_1;
        uint64_t a1;
      };

      using _Frame =
          std::variant<_Enter, _After_TNode, _After_TNode_1, _Combine_TNode>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified ternary_sum: _Enter -> _After_TNode -> _After_TNode_1 ->
      /// _Combine_TNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const ternary *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ternary::TLeaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename ternary::TNode>(_sv.v());
            _stack.emplace_back(_After_TNode{crane_raw(a2), crane_raw(a0), a1});
            _stack.emplace_back(_Enter{crane_raw(a3)});
          }
        } else if (std::holds_alternative<_After_TNode>(_frame)) {
          auto _f = std::move(std::get<_After_TNode>(_frame));
          _stack.emplace_back(_After_TNode_1{std::move(_result), _f.a0, _f.a1});
          _stack.emplace_back(_Enter{_f.a2});
        } else if (std::holds_alternative<_After_TNode_1>(_frame)) {
          auto _f = std::move(std::get<_After_TNode_1>(_frame));
          _stack.emplace_back(
              _Combine_TNode{_f._result, std::move(_result), _f.a1});
          _stack.emplace_back(_Enter{_f.a0});
        } else {
          auto _f = std::move(std::get<_Combine_TNode>(_frame));
          _result =
              (((std::move(_result) + _f.a1) + _f._result_1) + _f._result_0);
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, ternary &, T1 &, uint64_t &,
                                     ternary &, T1 &, ternary &, T1 &>
    T1 ternary_rec(T1 f, F1 &&f0) const {
      const ternary *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const ternary *_self;
      };

      /// _After_TNode: saves [a2_0, a0_0, a3, a2_1, a1, a0_1], dispatches next
      /// recursive call.
      struct _After_TNode {
        const ternary *a2_0;
        const ternary *a0_0;
        ternary a3;
        ternary a2_1;
        uint64_t a1;
        ternary a0_1;
      };

      /// _After_TNode_1: saves [_result, a0_0, a3, a2, a1, a0_1], dispatches
      /// next recursive call.
      struct _After_TNode_1 {
        std::decay_t<T1> _result;
        const ternary *a0_0;
        ternary a3;
        ternary a2;
        uint64_t a1;
        ternary a0_1;
      };

      /// _Combine_TNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_TNode {
        std::decay_t<T1> _result_0;
        std::decay_t<T1> _result_1;
        ternary a3;
        ternary a2;
        uint64_t a1;
        ternary a0;
      };

      using _Frame =
          std::variant<_Enter, _After_TNode, _After_TNode_1, _Combine_TNode>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified ternary_rec: _Enter -> _After_TNode -> _After_TNode_1 ->
      /// _Combine_TNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const ternary *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ternary::TLeaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename ternary::TNode>(_sv.v());
            _stack.emplace_back(
                _After_TNode{crane_raw(a2), crane_raw(a0), *a3, *a2, a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a3)});
          }
        } else if (std::holds_alternative<_After_TNode>(_frame)) {
          auto _f = std::move(std::get<_After_TNode>(_frame));
          _stack.emplace_back(
              _After_TNode_1{std::move(_result), _f.a0_0, std::move(_f.a3),
                             std::move(_f.a2_1), _f.a1, std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a2_0});
        } else if (std::holds_alternative<_After_TNode_1>(_frame)) {
          auto _f = std::move(std::get<_After_TNode_1>(_frame));
          _stack.emplace_back(_Combine_TNode{
              std::move(_f._result), std::move(_result), std::move(_f.a3),
              std::move(_f.a2), _f.a1, std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else {
          auto _f = std::move(std::get<_Combine_TNode>(_frame));
          _result = f0(std::move(_f.a0), std::move(_result), _f.a1,
                       std::move(_f.a2), std::move(_f._result_1),
                       std::move(_f.a3), std::move(_f._result_0));
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, ternary &, T1 &, uint64_t &,
                                     ternary &, T1 &, ternary &, T1 &>
    T1 ternary_rect(T1 f, F1 &&f0) const {
      const ternary *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const ternary *_self;
      };

      /// _After_TNode: saves [a2_0, a0_0, a3, a2_1, a1, a0_1], dispatches next
      /// recursive call.
      struct _After_TNode {
        const ternary *a2_0;
        const ternary *a0_0;
        ternary a3;
        ternary a2_1;
        uint64_t a1;
        ternary a0_1;
      };

      /// _After_TNode_1: saves [_result, a0_0, a3, a2, a1, a0_1], dispatches
      /// next recursive call.
      struct _After_TNode_1 {
        std::decay_t<T1> _result;
        const ternary *a0_0;
        ternary a3;
        ternary a2;
        uint64_t a1;
        ternary a0_1;
      };

      /// _Combine_TNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_TNode {
        std::decay_t<T1> _result_0;
        std::decay_t<T1> _result_1;
        ternary a3;
        ternary a2;
        uint64_t a1;
        ternary a0;
      };

      using _Frame =
          std::variant<_Enter, _After_TNode, _After_TNode_1, _Combine_TNode>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified ternary_rect: _Enter -> _After_TNode -> _After_TNode_1 ->
      /// _Combine_TNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const ternary *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ternary::TLeaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename ternary::TNode>(_sv.v());
            _stack.emplace_back(
                _After_TNode{crane_raw(a2), crane_raw(a0), *a3, *a2, a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a3)});
          }
        } else if (std::holds_alternative<_After_TNode>(_frame)) {
          auto _f = std::move(std::get<_After_TNode>(_frame));
          _stack.emplace_back(
              _After_TNode_1{std::move(_result), _f.a0_0, std::move(_f.a3),
                             std::move(_f.a2_1), _f.a1, std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a2_0});
        } else if (std::holds_alternative<_After_TNode_1>(_frame)) {
          auto _f = std::move(std::get<_After_TNode_1>(_frame));
          _stack.emplace_back(_Combine_TNode{
              std::move(_f._result), std::move(_result), std::move(_f.a3),
              std::move(_f.a2), _f.a1, std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else {
          auto _f = std::move(std::get<_Combine_TNode>(_frame));
          _result = f0(std::move(_f.a0), std::move(_result), _f.a1,
                       std::move(_f.a2), std::move(_f._result_1),
                       std::move(_f.a3), std::move(_f._result_0));
        }
      }
      return _result;
    }
  };

  struct quadtree {
    // TYPES
    struct QLeaf {
      uint64_t a0;
    };

    struct Quad {
      std::shared_ptr<quadtree> a0;
      std::shared_ptr<quadtree> a1;
      std::shared_ptr<quadtree> a2;
      std::shared_ptr<quadtree> a3;
    };

    using variant_t = std::variant<QLeaf, Quad>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    quadtree() {}

    explicit quadtree(QLeaf _v) : v_(std::move(_v)) {}

    explicit quadtree(Quad _v) : v_(std::move(_v)) {}

    static quadtree qleaf(uint64_t a0) { return quadtree(QLeaf{a0}); }

    static quadtree quad(quadtree a0, quadtree a1, quadtree a2, quadtree a3) {
      return quadtree(Quad{std::make_shared<quadtree>(std::move(a0)),
                           std::make_shared<quadtree>(std::move(a1)),
                           std::make_shared<quadtree>(std::move(a2)),
                           std::make_shared<quadtree>(std::move(a3))});
    }

    // MANIPULATORS
    ~quadtree() {
      crane::small_vector<std::shared_ptr<quadtree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Quad>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
          if (_alt->a2) {
            _stack.push_back(std::move(_alt->a2));
          }
          if (_alt->a3) {
            _stack.push_back(std::move(_alt->a3));
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

    quadtree(const quadtree &) = default;
    quadtree &operator=(const quadtree &) = default;
    quadtree(quadtree &&) noexcept = default;
    quadtree &operator=(quadtree &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t quad_sum() const {
      const quadtree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const quadtree *_self;
      };

      /// _After_Quad: saves [a2, a1, a0], dispatches next recursive call.
      struct _After_Quad {
        const quadtree *a2;
        const quadtree *a1;
        const quadtree *a0;
      };

      /// _After_Quad_1: saves [_result, a1, a0], dispatches next recursive
      /// call.
      struct _After_Quad_1 {
        uint64_t _result;
        const quadtree *a1;
        const quadtree *a0;
      };

      /// _After_Quad_2: saves [_result_0, _result_1, a0], dispatches next
      /// recursive call.
      struct _After_Quad_2 {
        uint64_t _result_0;
        uint64_t _result_1;
        const quadtree *a0;
      };

      /// _Combine_Quad: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Quad {
        uint64_t _result_0;
        uint64_t _result_1;
        uint64_t _result_2;
      };

      using _Frame = std::variant<_Enter, _After_Quad, _After_Quad_1,
                                  _After_Quad_2, _Combine_Quad>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified quad_sum: _Enter -> _After_Quad -> _After_Quad_1 ->
      /// _After_Quad_2 -> _Combine_Quad.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const quadtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename quadtree::QLeaf>(_sv.v());
            _result = std::move(a0);
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename quadtree::Quad>(_sv.v());
            _stack.emplace_back(
                _After_Quad{crane_raw(a2), crane_raw(a1), crane_raw(a0)});
            _stack.emplace_back(_Enter{crane_raw(a3)});
          }
        } else if (std::holds_alternative<_After_Quad>(_frame)) {
          auto _f = std::move(std::get<_After_Quad>(_frame));
          _stack.emplace_back(_After_Quad_1{std::move(_result), _f.a1, _f.a0});
          _stack.emplace_back(_Enter{_f.a2});
        } else if (std::holds_alternative<_After_Quad_1>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_1>(_frame));
          _stack.emplace_back(
              _After_Quad_2{_f._result, std::move(_result), _f.a0});
          _stack.emplace_back(_Enter{_f.a1});
        } else if (std::holds_alternative<_After_Quad_2>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_2>(_frame));
          _stack.emplace_back(
              _Combine_Quad{_f._result_0, _f._result_1, std::move(_result)});
          _stack.emplace_back(_Enter{_f.a0});
        } else {
          auto _f = std::move(std::get<_Combine_Quad>(_frame));
          _result = (((std::move(_result) + _f._result_2) + _f._result_1) +
                     _f._result_0);
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, quadtree &, T1 &, quadtree &,
                                     T1 &, quadtree &, T1 &, quadtree &, T1 &>
    T1 quadtree_rec(F0 &&f, F1 &&f0) const {
      const quadtree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const quadtree *_self;
      };

      /// _After_Quad: saves [a2_0, a1_0, a0_0, a3, a2_1, a1_1, a0_1],
      /// dispatches next recursive call.
      struct _After_Quad {
        const quadtree *a2_0;
        const quadtree *a1_0;
        const quadtree *a0_0;
        quadtree a3;
        quadtree a2_1;
        quadtree a1_1;
        quadtree a0_1;
      };

      /// _After_Quad_1: saves [_result, a1_0, a0_0, a3, a2, a1_1, a0_1],
      /// dispatches next recursive call.
      struct _After_Quad_1 {
        std::decay_t<T1> _result;
        const quadtree *a1_0;
        const quadtree *a0_0;
        quadtree a3;
        quadtree a2;
        quadtree a1_1;
        quadtree a0_1;
      };

      /// _After_Quad_2: saves [_result_0, _result_1, a0_0, a3, a2, a1, a0_1],
      /// dispatches next recursive call.
      struct _After_Quad_2 {
        std::decay_t<T1> _result_0;
        std::decay_t<T1> _result_1;
        const quadtree *a0_0;
        quadtree a3;
        quadtree a2;
        quadtree a1;
        quadtree a0_1;
      };

      /// _Combine_Quad: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Quad {
        std::decay_t<T1> _result_0;
        std::decay_t<T1> _result_1;
        std::decay_t<T1> _result_2;
        quadtree a3;
        quadtree a2;
        quadtree a1;
        quadtree a0;
      };

      using _Frame = std::variant<_Enter, _After_Quad, _After_Quad_1,
                                  _After_Quad_2, _Combine_Quad>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified quadtree_rec: _Enter -> _After_Quad -> _After_Quad_1 ->
      /// _After_Quad_2 -> _Combine_Quad.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const quadtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename quadtree::QLeaf>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename quadtree::Quad>(_sv.v());
            _stack.emplace_back(_After_Quad{crane_raw(a2), crane_raw(a1),
                                            crane_raw(a0), *a3, *a2, *a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a3)});
          }
        } else if (std::holds_alternative<_After_Quad>(_frame)) {
          auto _f = std::move(std::get<_After_Quad>(_frame));
          _stack.emplace_back(_After_Quad_1{
              std::move(_result), _f.a1_0, _f.a0_0, std::move(_f.a3),
              std::move(_f.a2_1), std::move(_f.a1_1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a2_0});
        } else if (std::holds_alternative<_After_Quad_1>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_1>(_frame));
          _stack.emplace_back(
              _After_Quad_2{std::move(_f._result), std::move(_result), _f.a0_0,
                            std::move(_f.a3), std::move(_f.a2),
                            std::move(_f.a1_1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a1_0});
        } else if (std::holds_alternative<_After_Quad_2>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_2>(_frame));
          _stack.emplace_back(_Combine_Quad{
              std::move(_f._result_0), std::move(_f._result_1),
              std::move(_result), std::move(_f.a3), std::move(_f.a2),
              std::move(_f.a1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else {
          auto _f = std::move(std::get<_Combine_Quad>(_frame));
          _result = f0(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f._result_2), std::move(_f.a2),
                       std::move(_f._result_1), std::move(_f.a3),
                       std::move(_f._result_0));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, quadtree &, T1 &, quadtree &,
                                     T1 &, quadtree &, T1 &, quadtree &, T1 &>
    T1 quadtree_rect(F0 &&f, F1 &&f0) const {
      const quadtree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const quadtree *_self;
      };

      /// _After_Quad: saves [a2_0, a1_0, a0_0, a3, a2_1, a1_1, a0_1],
      /// dispatches next recursive call.
      struct _After_Quad {
        const quadtree *a2_0;
        const quadtree *a1_0;
        const quadtree *a0_0;
        quadtree a3;
        quadtree a2_1;
        quadtree a1_1;
        quadtree a0_1;
      };

      /// _After_Quad_1: saves [_result, a1_0, a0_0, a3, a2, a1_1, a0_1],
      /// dispatches next recursive call.
      struct _After_Quad_1 {
        std::decay_t<T1> _result;
        const quadtree *a1_0;
        const quadtree *a0_0;
        quadtree a3;
        quadtree a2;
        quadtree a1_1;
        quadtree a0_1;
      };

      /// _After_Quad_2: saves [_result_0, _result_1, a0_0, a3, a2, a1, a0_1],
      /// dispatches next recursive call.
      struct _After_Quad_2 {
        std::decay_t<T1> _result_0;
        std::decay_t<T1> _result_1;
        const quadtree *a0_0;
        quadtree a3;
        quadtree a2;
        quadtree a1;
        quadtree a0_1;
      };

      /// _Combine_Quad: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Quad {
        std::decay_t<T1> _result_0;
        std::decay_t<T1> _result_1;
        std::decay_t<T1> _result_2;
        quadtree a3;
        quadtree a2;
        quadtree a1;
        quadtree a0;
      };

      using _Frame = std::variant<_Enter, _After_Quad, _After_Quad_1,
                                  _After_Quad_2, _Combine_Quad>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified quadtree_rect: _Enter -> _After_Quad -> _After_Quad_1 ->
      /// _After_Quad_2 -> _Combine_Quad.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const quadtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename quadtree::QLeaf>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename quadtree::Quad>(_sv.v());
            _stack.emplace_back(_After_Quad{crane_raw(a2), crane_raw(a1),
                                            crane_raw(a0), *a3, *a2, *a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a3)});
          }
        } else if (std::holds_alternative<_After_Quad>(_frame)) {
          auto _f = std::move(std::get<_After_Quad>(_frame));
          _stack.emplace_back(_After_Quad_1{
              std::move(_result), _f.a1_0, _f.a0_0, std::move(_f.a3),
              std::move(_f.a2_1), std::move(_f.a1_1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a2_0});
        } else if (std::holds_alternative<_After_Quad_1>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_1>(_frame));
          _stack.emplace_back(
              _After_Quad_2{std::move(_f._result), std::move(_result), _f.a0_0,
                            std::move(_f.a3), std::move(_f.a2),
                            std::move(_f.a1_1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a1_0});
        } else if (std::holds_alternative<_After_Quad_2>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_2>(_frame));
          _stack.emplace_back(_Combine_Quad{
              std::move(_f._result_0), std::move(_f._result_1),
              std::move(_result), std::move(_f.a3), std::move(_f.a2),
              std::move(_f.a1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else {
          auto _f = std::move(std::get<_Combine_Quad>(_frame));
          _result = f0(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f._result_2), std::move(_f.a2),
                       std::move(_f._result_1), std::move(_f.a3),
                       std::move(_f._result_0));
        }
      }
      return _result;
    }
  };

  struct leaf_tree {
    // TYPES
    struct LLeaf {
      uint64_t a0;
    };

    struct LNode {
      std::shared_ptr<leaf_tree> a0;
      std::shared_ptr<leaf_tree> a1;
    };

    using variant_t = std::variant<LLeaf, LNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    leaf_tree() {}

    explicit leaf_tree(LLeaf _v) : v_(std::move(_v)) {}

    explicit leaf_tree(LNode _v) : v_(std::move(_v)) {}

    static leaf_tree lleaf(uint64_t a0) { return leaf_tree(LLeaf{a0}); }

    static leaf_tree lnode(leaf_tree a0, leaf_tree a1) {
      return leaf_tree(LNode{std::make_shared<leaf_tree>(std::move(a0)),
                             std::make_shared<leaf_tree>(std::move(a1))});
    }

    // MANIPULATORS
    ~leaf_tree() {
      crane::small_vector<std::shared_ptr<leaf_tree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<LNode>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
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

    leaf_tree(const leaf_tree &) = default;
    leaf_tree &operator=(const leaf_tree &) = default;
    leaf_tree(leaf_tree &&) noexcept = default;
    leaf_tree &operator=(leaf_tree &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t leaf_tree_max() const {
      const leaf_tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const leaf_tree *_self;
      };

      /// _Cont_LNode: saves [a1], resumes after recursive call, then processes
      /// rest.
      struct _Cont_LNode {
        std::shared_ptr<leaf_tree> a1;
      };

      /// _Cont_LNode_1: saves [lmax], resumes after recursive call, then
      /// processes rest.
      struct _Cont_LNode_1 {
        uint64_t lmax;
      };

      using _Frame = std::variant<_Enter, _Cont_LNode, _Cont_LNode_1>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified leaf_tree_max: _Enter -> _Cont_LNode -> _Cont_LNode_1.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const leaf_tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename leaf_tree::LLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename leaf_tree::LLeaf>(_sv.v());
            _result = std::move(a0);
          } else {
            const auto &[a0, a1] = std::get<typename leaf_tree::LNode>(_sv.v());
            _stack.emplace_back(_Cont_LNode{a1});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_Cont_LNode>(_frame)) {
          auto _f = std::move(std::get<_Cont_LNode>(_frame));
          std::shared_ptr<leaf_tree> a1 = std::move(_f.a1);
          uint64_t lmax = std::move(_result);
          _stack.emplace_back(_Cont_LNode_1{lmax});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<_Cont_LNode_1>(_frame));
          uint64_t lmax = _f.lmax;
          uint64_t rmax = std::move(_result);
          if (lmax < rmax) {
            _result = std::move(rmax);
          } else {
            _result = std::move(lmax);
          }
        }
      }
      return _result;
    }

    uint64_t leaf_tree_sum() const {
      const leaf_tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const leaf_tree *_self;
      };

      /// _After_LNode: saves [a0], dispatches next recursive call.
      struct _After_LNode {
        leaf_tree *a0;
      };

      /// _Combine_LNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_LNode {
        uint64_t _result;
      };

      using _Frame = std::variant<_Enter, _After_LNode, _Combine_LNode>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified leaf_tree_sum: _Enter -> _After_LNode -> _Combine_LNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const leaf_tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename leaf_tree::LLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename leaf_tree::LLeaf>(_sv.v());
            _result = std::move(a0);
          } else {
            const auto &[a0, a1] = std::get<typename leaf_tree::LNode>(_sv.v());
            _stack.emplace_back(_After_LNode{crane_raw(a0)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else if (std::holds_alternative<_After_LNode>(_frame)) {
          auto _f = std::move(std::get<_After_LNode>(_frame));
          _stack.emplace_back(_Combine_LNode{std::move(_result)});
          _stack.emplace_back(_Enter{_f.a0});
        } else {
          auto _f = std::move(std::get<_Combine_LNode>(_frame));
          _result = (std::move(_result) + std::move(_f._result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, leaf_tree &, T1 &, leaf_tree &,
                                     T1 &>
    T1 leaf_tree_rec(F0 &&f, F1 &&f0) const {
      const leaf_tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const leaf_tree *_self;
      };

      /// _After_LNode: saves [a0_0, a1, a0_1], dispatches next recursive call.
      struct _After_LNode {
        leaf_tree *a0_0;
        leaf_tree a1;
        leaf_tree a0_1;
      };

      /// _Combine_LNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_LNode {
        std::decay_t<T1> _result;
        leaf_tree a1;
        leaf_tree a0;
      };

      using _Frame = std::variant<_Enter, _After_LNode, _Combine_LNode>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified leaf_tree_rec: _Enter -> _After_LNode -> _Combine_LNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const leaf_tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename leaf_tree::LLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename leaf_tree::LLeaf>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1] = std::get<typename leaf_tree::LNode>(_sv.v());
            _stack.emplace_back(_After_LNode{crane_raw(a0), *a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else if (std::holds_alternative<_After_LNode>(_frame)) {
          auto _f = std::move(std::get<_After_LNode>(_frame));
          _stack.emplace_back(_Combine_LNode{
              std::move(_result), std::move(_f.a1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else {
          auto _f = std::move(std::get<_Combine_LNode>(_frame));
          _result = f0(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f._result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, leaf_tree &, T1 &, leaf_tree &,
                                     T1 &>
    T1 leaf_tree_rect(F0 &&f, F1 &&f0) const {
      const leaf_tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const leaf_tree *_self;
      };

      /// _After_LNode: saves [a0_0, a1, a0_1], dispatches next recursive call.
      struct _After_LNode {
        leaf_tree *a0_0;
        leaf_tree a1;
        leaf_tree a0_1;
      };

      /// _Combine_LNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_LNode {
        std::decay_t<T1> _result;
        leaf_tree a1;
        leaf_tree a0;
      };

      using _Frame = std::variant<_Enter, _After_LNode, _Combine_LNode>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified leaf_tree_rect: _Enter -> _After_LNode -> _Combine_LNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const leaf_tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename leaf_tree::LLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename leaf_tree::LLeaf>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1] = std::get<typename leaf_tree::LNode>(_sv.v());
            _stack.emplace_back(_After_LNode{crane_raw(a0), *a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else if (std::holds_alternative<_After_LNode>(_frame)) {
          auto _f = std::move(std::get<_After_LNode>(_frame));
          _stack.emplace_back(_Combine_LNode{
              std::move(_result), std::move(_f.a1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else {
          auto _f = std::move(std::get<_Combine_LNode>(_frame));
          _result = f0(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f._result));
        }
      }
      return _result;
    }
  };
};

#endif // INCLUDED_LOOPIFY_TREE_VARIANTS
