#pragma once

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
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

    static ternary tnode(crane::shared_child_slot<ternary> a0, uint64_t a1,
                         crane::shared_child_slot<ternary> a2,
                         crane::shared_child_slot<ternary> a3) {
      return ternary(TNode{a0.take(), a1, a2.take(), a3.take()});
    }

    // MANIPULATORS
    ~ternary() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<TLeaf>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<TNode>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a2 && _alt->a2.use_count() == 1) ||
              (_alt->a3 && _alt->a3.use_count() == 1))) {
          return;
        }
      }
      crane::small_vector<std::shared_ptr<ternary>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<TNode>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a2 && _alt->a2.use_count() == 1) {
            _stack.push_back(std::move(_alt->a2));
          }
          if (_alt->a3 && _alt->a3.use_count() == 1) {
            _stack.push_back(std::move(_alt->a3));
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

    ternary(const ternary &) = default;
    ternary &operator=(const ternary &) = default;
    ternary(ternary &&) = default;
    ternary &operator=(ternary &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t ternary_count() const {
      const ternary *_self = this;

      // Explicit stack replaces the non-tail recursion of ternary_count: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const ternary *_self;
      };

      struct _after_ternary_count_in_TNode {
        const ternary *a2;
        const ternary *a3;
      };

      struct _after_ternary_count_in_TNode_2 {
        const ternary *a3;
        uint64_t _tmp3;
      };

      struct _after_ternary_count_in_TNode_3 {
        uint64_t _tmp3;
        uint64_t _tmp2;
      };

      using _frame = std::variant<_call, _after_ternary_count_in_TNode,
                                  _after_ternary_count_in_TNode_2,
                                  _after_ternary_count_in_TNode_3>;
      uint64_t _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const ternary *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ternary::TLeaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, _, a2, a3] =
                std::get<typename ternary::TNode>(_sv.v());
            _stack.emplace_back(
                _after_ternary_count_in_TNode{crane_raw(a2), crane_raw(a3)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (
                std::holds_alternative<_after_ternary_count_in_TNode>(_popped)) {
          auto _f = std::move(std::get<_after_ternary_count_in_TNode>(_popped));
          _stack.pop_back();
          const ternary &a2 = *_f.a2;
          const ternary &a3 = *_f.a3;
          _stack.emplace_back(_after_ternary_count_in_TNode_2{&a3, _result});
          _stack.emplace_back(_call{_f.a2});
        } else if (std::holds_alternative<_after_ternary_count_in_TNode_2>(
                       _popped)) {
          auto _f =
              std::move(std::get<_after_ternary_count_in_TNode_2>(_popped));
          _stack.pop_back();
          const ternary &a3 = *_f.a3;
          _stack.emplace_back(
              _after_ternary_count_in_TNode_3{_f._tmp3, _result});
          _stack.emplace_back(_call{_f.a3});
        } else {
          auto _f =
              std::move(std::get<_after_ternary_count_in_TNode_3>(_popped));
          _stack.pop_back();
          _result = UINT64_C(1) + _f._tmp3 + _f._tmp2 + _result;
        }
      }
      return _result;
    }

    uint64_t ternary_sum() const {
      const ternary *_self = this;

      // Explicit stack replaces the non-tail recursion of ternary_sum: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const ternary *_self;
      };

      struct _after_ternary_sum_in_TNode {
        uint64_t a1;
        const ternary *a2;
        const ternary *a3;
      };

      struct _after_ternary_sum_in_TNode_2 {
        uint64_t a1;
        const ternary *a3;
        uint64_t _tmp3;
      };

      struct _after_ternary_sum_in_TNode_3 {
        uint64_t a1;
        uint64_t _tmp3;
        uint64_t _tmp2;
      };

      using _frame = std::variant<_call, _after_ternary_sum_in_TNode,
                                  _after_ternary_sum_in_TNode_2,
                                  _after_ternary_sum_in_TNode_3>;
      uint64_t _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const ternary *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ternary::TLeaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename ternary::TNode>(_sv.v());
            _stack.emplace_back(
                _after_ternary_sum_in_TNode{a1, crane_raw(a2), crane_raw(a3)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_ternary_sum_in_TNode>(_popped)) {
          auto _f = std::move(std::get<_after_ternary_sum_in_TNode>(_popped));
          _stack.pop_back();
          uint64_t a1 = _f.a1;
          const ternary &a2 = *_f.a2;
          const ternary &a3 = *_f.a3;
          _stack.emplace_back(_after_ternary_sum_in_TNode_2{a1, &a3, _result});
          _stack.emplace_back(_call{_f.a2});
        } else if (
                std::holds_alternative<_after_ternary_sum_in_TNode_2>(_popped)) {
          auto _f = std::move(std::get<_after_ternary_sum_in_TNode_2>(_popped));
          _stack.pop_back();
          uint64_t a1 = _f.a1;
          const ternary &a3 = *_f.a3;
          _stack.emplace_back(
              _after_ternary_sum_in_TNode_3{a1, _f._tmp3, _result});
          _stack.emplace_back(_call{_f.a3});
        } else {
          auto _f = std::move(std::get<_after_ternary_sum_in_TNode_3>(_popped));
          _stack.pop_back();
          uint64_t a1 = _f.a1;
          _result = _f._tmp3 + a1 + _f._tmp2 + _result;
        }
      }
      return _result;
    }

    template <typename T1, typename F1> T1 ternary_rec(T1 f, F1 &&f0) const {
      return this->template ternary_rect<T1>(std::move(f), f0);
    }

    template <typename T1, typename F1> T1 ternary_rect(T1 f, F1 &&f0) const {
      const ternary *_self = this;

      // Explicit stack replaces the non-tail recursion of ternary_rect: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const ternary *_self;
      };

      struct _after_ternary_rect_in_TNode {
        std::shared_ptr<ternary> a0;
        uint64_t a1;
        const ternary *a2;
        const ternary *a3;
      };

      struct _after_ternary_rect_in_TNode_2 {
        std::shared_ptr<ternary> a0;
        uint64_t a1;
        const ternary *a2;
        const ternary *a3;
        T1 _tmp3;
      };

      struct _after_ternary_rect_in_TNode_3 {
        std::shared_ptr<ternary> a0;
        uint64_t a1;
        const ternary *a2;
        const ternary *a3;
        T1 _tmp3;
        T1 _tmp2;
      };

      using _frame = std::variant<_call, _after_ternary_rect_in_TNode,
                                  _after_ternary_rect_in_TNode_2,
                                  _after_ternary_rect_in_TNode_3>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const ternary *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ternary::TLeaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename ternary::TNode>(_sv.v());
            _stack.emplace_back(_after_ternary_rect_in_TNode{
                a0, a1, crane_raw(a2), crane_raw(a3)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (
                std::holds_alternative<_after_ternary_rect_in_TNode>(_popped)) {
          auto _f = std::move(std::get<_after_ternary_rect_in_TNode>(_popped));
          _stack.pop_back();
          std::shared_ptr<ternary> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          const ternary &a2 = *_f.a2;
          const ternary &a3 = *_f.a3;
          _stack.emplace_back(_after_ternary_rect_in_TNode_2{
              std::move(a0), a1, &a2, &a3, std::move(_result)});
          _stack.emplace_back(_call{_f.a2});
        } else if (
                std::holds_alternative<_after_ternary_rect_in_TNode_2>(_popped)) {
          auto _f =
              std::move(std::get<_after_ternary_rect_in_TNode_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<ternary> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          const ternary &a2 = *_f.a2;
          const ternary &a3 = *_f.a3;
          _stack.emplace_back(_after_ternary_rect_in_TNode_3{
              std::move(a0), a1, &a2, &a3, std::move(_f._tmp3),
              std::move(_result)});
          _stack.emplace_back(_call{_f.a3});
        } else {
          auto _f =
              std::move(std::get<_after_ternary_rect_in_TNode_3>(_popped));
          _stack.pop_back();
          std::shared_ptr<ternary> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          const ternary &a2 = *_f.a2;
          const ternary &a3 = *_f.a3;
          _result = f0(*a0, std::move(_f._tmp3), a1, a2, std::move(_f._tmp2),
                       a3, std::move(_result));
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

    static quadtree quad(crane::shared_child_slot<quadtree> a0,
                         crane::shared_child_slot<quadtree> a1,
                         crane::shared_child_slot<quadtree> a2,
                         crane::shared_child_slot<quadtree> a3) {
      return quadtree(Quad{a0.take(), a1.take(), a2.take(), a3.take()});
    }

    // MANIPULATORS
    ~quadtree() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<QLeaf>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<Quad>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a1 && _alt->a1.use_count() == 1) ||
              (_alt->a2 && _alt->a2.use_count() == 1) ||
              (_alt->a3 && _alt->a3.use_count() == 1))) {
          return;
        }
      }
      crane::small_vector<std::shared_ptr<quadtree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Quad>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            _stack.push_back(std::move(_alt->a1));
          }
          if (_alt->a2 && _alt->a2.use_count() == 1) {
            _stack.push_back(std::move(_alt->a2));
          }
          if (_alt->a3 && _alt->a3.use_count() == 1) {
            _stack.push_back(std::move(_alt->a3));
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

    quadtree(const quadtree &) = default;
    quadtree &operator=(const quadtree &) = default;
    quadtree(quadtree &&) = default;
    quadtree &operator=(quadtree &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t quad_sum() const {
      const quadtree *_self = this;

      // Explicit stack replaces the non-tail recursion of quad_sum: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const quadtree *_self;
      };

      struct _after_quad_sum_in_Quad {
        const quadtree *a1;
        const quadtree *a2;
        const quadtree *a3;
      };

      struct _after_quad_sum_in_Quad_2 {
        const quadtree *a2;
        const quadtree *a3;
        uint64_t _tmp4;
      };

      struct _after_quad_sum_in_Quad_3 {
        const quadtree *a3;
        uint64_t _tmp4;
        uint64_t _tmp3;
      };

      struct _after_quad_sum_in_Quad_4 {
        uint64_t _tmp4;
        uint64_t _tmp3;
        uint64_t _tmp2;
      };

      using _frame = std::variant<
          _call, _after_quad_sum_in_Quad, _after_quad_sum_in_Quad_2,
          _after_quad_sum_in_Quad_3, _after_quad_sum_in_Quad_4>;
      uint64_t _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const quadtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename quadtree::QLeaf>(_sv.v());
            _result = std::move(a0);
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename quadtree::Quad>(_sv.v());
            _stack.emplace_back(_after_quad_sum_in_Quad{
                crane_raw(a1), crane_raw(a2), crane_raw(a3)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_quad_sum_in_Quad>(_popped)) {
          auto _f = std::move(std::get<_after_quad_sum_in_Quad>(_popped));
          _stack.pop_back();
          const quadtree &a1 = *_f.a1;
          const quadtree &a2 = *_f.a2;
          const quadtree &a3 = *_f.a3;
          _stack.emplace_back(_after_quad_sum_in_Quad_2{&a2, &a3, _result});
          _stack.emplace_back(_call{_f.a1});
        } else if (std::holds_alternative<_after_quad_sum_in_Quad_2>(_popped)) {
          auto _f = std::move(std::get<_after_quad_sum_in_Quad_2>(_popped));
          _stack.pop_back();
          const quadtree &a2 = *_f.a2;
          const quadtree &a3 = *_f.a3;
          _stack.emplace_back(_after_quad_sum_in_Quad_3{&a3, _f._tmp4,
                                                        _result});
          _stack.emplace_back(_call{_f.a2});
        } else if (std::holds_alternative<_after_quad_sum_in_Quad_3>(_popped)) {
          auto _f = std::move(std::get<_after_quad_sum_in_Quad_3>(_popped));
          _stack.pop_back();
          const quadtree &a3 = *_f.a3;
          _stack.emplace_back(
              _after_quad_sum_in_Quad_4{_f._tmp4, _f._tmp3, _result});
          _stack.emplace_back(_call{_f.a3});
        } else {
          auto _f = std::move(std::get<_after_quad_sum_in_Quad_4>(_popped));
          _stack.pop_back();
          _result = _f._tmp4 + _f._tmp3 + _f._tmp2 + _result;
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
    T1 quadtree_rec(F0 &&f, F1 &&f0) const {
      return this->template quadtree_rect<T1>(f, f0);
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
    T1 quadtree_rect(F0 &&f, F1 &&f0) const {
      const quadtree *_self = this;

      // Explicit stack replaces the non-tail recursion of quadtree_rect: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const quadtree *_self;
      };

      struct _after_quadtree_rect_in_Quad {
        std::shared_ptr<quadtree> a0;
        const quadtree *a1;
        const quadtree *a2;
        const quadtree *a3;
      };

      struct _after_quadtree_rect_in_Quad_2 {
        std::shared_ptr<quadtree> a0;
        const quadtree *a1;
        const quadtree *a2;
        const quadtree *a3;
        T1 _tmp4;
      };

      struct _after_quadtree_rect_in_Quad_3 {
        std::shared_ptr<quadtree> a0;
        const quadtree *a1;
        const quadtree *a2;
        const quadtree *a3;
        T1 _tmp4;
        T1 _tmp3;
      };

      struct _after_quadtree_rect_in_Quad_4 {
        std::shared_ptr<quadtree> a0;
        const quadtree *a1;
        const quadtree *a2;
        const quadtree *a3;
        T1 _tmp4;
        T1 _tmp3;
        T1 _tmp2;
      };

      using _frame = std::variant<
          _call, _after_quadtree_rect_in_Quad, _after_quadtree_rect_in_Quad_2,
          _after_quadtree_rect_in_Quad_3, _after_quadtree_rect_in_Quad_4>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const quadtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename quadtree::QLeaf>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename quadtree::Quad>(_sv.v());
            _stack.emplace_back(_after_quadtree_rect_in_Quad{
                a0, crane_raw(a1), crane_raw(a2), crane_raw(a3)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (
                std::holds_alternative<_after_quadtree_rect_in_Quad>(_popped)) {
          auto _f = std::move(std::get<_after_quadtree_rect_in_Quad>(_popped));
          _stack.pop_back();
          std::shared_ptr<quadtree> a0 = std::move(_f.a0);
          const quadtree &a1 = *_f.a1;
          const quadtree &a2 = *_f.a2;
          const quadtree &a3 = *_f.a3;
          _stack.emplace_back(_after_quadtree_rect_in_Quad_2{
              std::move(a0), &a1, &a2, &a3, std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else if (
                std::holds_alternative<_after_quadtree_rect_in_Quad_2>(_popped)) {
          auto _f =
              std::move(std::get<_after_quadtree_rect_in_Quad_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<quadtree> a0 = std::move(_f.a0);
          const quadtree &a1 = *_f.a1;
          const quadtree &a2 = *_f.a2;
          const quadtree &a3 = *_f.a3;
          _stack.emplace_back(_after_quadtree_rect_in_Quad_3{
              std::move(a0), &a1, &a2, &a3, std::move(_f._tmp4),
              std::move(_result)});
          _stack.emplace_back(_call{_f.a2});
        } else if (
                std::holds_alternative<_after_quadtree_rect_in_Quad_3>(_popped)) {
          auto _f =
              std::move(std::get<_after_quadtree_rect_in_Quad_3>(_popped));
          _stack.pop_back();
          std::shared_ptr<quadtree> a0 = std::move(_f.a0);
          const quadtree &a1 = *_f.a1;
          const quadtree &a2 = *_f.a2;
          const quadtree &a3 = *_f.a3;
          _stack.emplace_back(_after_quadtree_rect_in_Quad_4{
              std::move(a0), &a1, &a2, &a3, std::move(_f._tmp4),
              std::move(_f._tmp3), std::move(_result)});
          _stack.emplace_back(_call{_f.a3});
        } else {
          auto _f =
              std::move(std::get<_after_quadtree_rect_in_Quad_4>(_popped));
          _stack.pop_back();
          std::shared_ptr<quadtree> a0 = std::move(_f.a0);
          const quadtree &a1 = *_f.a1;
          const quadtree &a2 = *_f.a2;
          const quadtree &a3 = *_f.a3;
          _result = f0(*a0, std::move(_f._tmp4), a1, std::move(_f._tmp3), a2,
                       std::move(_f._tmp2), a3, std::move(_result));
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

    static leaf_tree lnode(crane::shared_child_slot<leaf_tree> a0,
                           crane::shared_child_slot<leaf_tree> a1) {
      return leaf_tree(LNode{a0.take(), a1.take()});
    }

    // MANIPULATORS
    ~leaf_tree() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<LLeaf>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<LNode>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a1 && _alt->a1.use_count() == 1))) {
          return;
        }
      }
      crane::small_vector<std::shared_ptr<leaf_tree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<LNode>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
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

    leaf_tree(const leaf_tree &) = default;
    leaf_tree &operator=(const leaf_tree &) = default;
    leaf_tree(leaf_tree &&) = default;
    leaf_tree &operator=(leaf_tree &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t leaf_tree_max() const {
      const leaf_tree *_self = this;

      // Explicit stack replaces the non-tail recursion of leaf_tree_max: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const leaf_tree *_self;
      };

      struct _after_leaf_tree_max_in_LNode {
        const leaf_tree *a1;
      };

      struct _after_leaf_tree_max_in_LNode_2 {
        uint64_t lmax;
      };

      using _frame = std::variant<_call, _after_leaf_tree_max_in_LNode,
                                  _after_leaf_tree_max_in_LNode_2>;
      uint64_t _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const leaf_tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename leaf_tree::LLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename leaf_tree::LLeaf>(_sv.v());
            _result = std::move(a0);
          } else {
            const auto &[a0, a1] = std::get<typename leaf_tree::LNode>(_sv.v());
            _stack.emplace_back(_after_leaf_tree_max_in_LNode{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (
                std::holds_alternative<_after_leaf_tree_max_in_LNode>(_popped)) {
          auto _f = std::move(std::get<_after_leaf_tree_max_in_LNode>(_popped));
          _stack.pop_back();
          const leaf_tree &a1 = *_f.a1;
          uint64_t lmax = _result;
          _stack.emplace_back(_after_leaf_tree_max_in_LNode_2{lmax});
          _stack.emplace_back(_call{_f.a1});
        } else {
          auto _f =
              std::move(std::get<_after_leaf_tree_max_in_LNode_2>(_popped));
          _stack.pop_back();
          uint64_t lmax = _f.lmax;
          uint64_t rmax = _result;
          if (lmax < rmax) {
            _result = rmax;
          } else {
            _result = lmax;
          }
        }
      }
      return _result;
    }

    uint64_t leaf_tree_sum() const {
      const leaf_tree *_self = this;

      // Explicit stack replaces the non-tail recursion of leaf_tree_sum: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const leaf_tree *_self;
      };

      struct _after_leaf_tree_sum_in_LNode {
        const leaf_tree *a1;
      };

      struct _after_leaf_tree_sum_in_LNode_2 {
        uint64_t _tmp2;
      };

      using _frame = std::variant<_call, _after_leaf_tree_sum_in_LNode,
                                  _after_leaf_tree_sum_in_LNode_2>;
      uint64_t _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const leaf_tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename leaf_tree::LLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename leaf_tree::LLeaf>(_sv.v());
            _result = std::move(a0);
          } else {
            const auto &[a0, a1] = std::get<typename leaf_tree::LNode>(_sv.v());
            _stack.emplace_back(_after_leaf_tree_sum_in_LNode{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (
                std::holds_alternative<_after_leaf_tree_sum_in_LNode>(_popped)) {
          auto _f = std::move(std::get<_after_leaf_tree_sum_in_LNode>(_popped));
          _stack.pop_back();
          const leaf_tree &a1 = *_f.a1;
          _stack.emplace_back(_after_leaf_tree_sum_in_LNode_2{_result});
          _stack.emplace_back(_call{_f.a1});
        } else {
          auto _f =
              std::move(std::get<_after_leaf_tree_sum_in_LNode_2>(_popped));
          _stack.pop_back();
          _result = _f._tmp2 + _result;
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
    T1 leaf_tree_rec(F0 &&f, F1 &&f0) const {
      return this->template leaf_tree_rect<T1>(f, f0);
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
    T1 leaf_tree_rect(F0 &&f, F1 &&f0) const {
      const leaf_tree *_self = this;

      // Explicit stack replaces the non-tail recursion of leaf_tree_rect: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const leaf_tree *_self;
      };

      struct _after_leaf_tree_rect_in_LNode {
        std::shared_ptr<leaf_tree> a0;
        const leaf_tree *a1;
      };

      struct _after_leaf_tree_rect_in_LNode_2 {
        std::shared_ptr<leaf_tree> a0;
        const leaf_tree *a1;
        T1 _tmp2;
      };

      using _frame = std::variant<_call, _after_leaf_tree_rect_in_LNode,
                                  _after_leaf_tree_rect_in_LNode_2>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const leaf_tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename leaf_tree::LLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename leaf_tree::LLeaf>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1] = std::get<typename leaf_tree::LNode>(_sv.v());
            _stack.emplace_back(
                _after_leaf_tree_rect_in_LNode{a0, crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (
                std::holds_alternative<_after_leaf_tree_rect_in_LNode>(_popped)) {
          auto _f =
              std::move(std::get<_after_leaf_tree_rect_in_LNode>(_popped));
          _stack.pop_back();
          std::shared_ptr<leaf_tree> a0 = std::move(_f.a0);
          const leaf_tree &a1 = *_f.a1;
          _stack.emplace_back(_after_leaf_tree_rect_in_LNode_2{
              std::move(a0), &a1, std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else {
          auto _f =
              std::move(std::get<_after_leaf_tree_rect_in_LNode_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<leaf_tree> a0 = std::move(_f.a0);
          const leaf_tree &a1 = *_f.a1;
          _result = f0(*a0, std::move(_f._tmp2), a1, std::move(_result));
        }
      }
      return _result;
    }
  };
};
