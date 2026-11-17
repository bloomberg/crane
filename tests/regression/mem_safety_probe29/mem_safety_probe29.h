#ifndef INCLUDED_MEM_SAFETY_PROBE29
#define INCLUDED_MEM_SAFETY_PROBE29

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct MemSafetyProbe29 {
  /// An inner tree type — value type with recursive children.
  struct inner {
    // TYPES
    struct ILeaf {};

    struct INode {
      std::shared_ptr<inner> a0;
      uint64_t a1;
      std::shared_ptr<inner> a2;
    };

    using variant_t = std::variant<ILeaf, INode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    inner() {}

    explicit inner(ILeaf _v) : v_(_v) {}

    explicit inner(INode _v) : v_(std::move(_v)) {}

    static inner ileaf() { return inner(ILeaf{}); }

    static inner inode(inner a0, uint64_t a1, inner a2) {
      return inner(INode{std::make_shared<inner>(std::move(a0)), a1,
                         std::make_shared<inner>(std::move(a2))});
    }

    // MANIPULATORS
    ~inner() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<ILeaf>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<INode>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a2 && _alt->a2.use_count() == 1))) {
          return;
        }
      }
      crane::small_vector<std::shared_ptr<inner>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<INode>(&_v)) {
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

    inner(const inner &) = default;
    inner &operator=(const inner &) = default;
    inner(inner &&) = default;
    inner &operator=(inner &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// TEST 3: Transform outer tree — rebuild with modified inner values.
    inner double_inner() const {
      const inner *_self = this;

      // Explicit stack replaces the non-tail recursion of double_inner: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const inner *_self;
      };

      struct _after_double_inner_in_INode {
        uint64_t a1;
        const inner *a2;
      };

      struct _after_double_inner_in_INode_2 {
        uint64_t a1;
        inner _tmp2;
      };

      using _frame = std::variant<_call, _after_double_inner_in_INode,
                                  _after_double_inner_in_INode_2>;
      inner _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const inner *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename inner::ILeaf>(_sv.v())) {
            _result = inner::ileaf();
          } else {
            const auto &[a0, a1, a2] = std::get<typename inner::INode>(_sv.v());
            _stack.emplace_back(_after_double_inner_in_INode{a1,
                                                             crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (
                std::holds_alternative<_after_double_inner_in_INode>(_popped)) {
          auto _f = std::move(std::get<_after_double_inner_in_INode>(_popped));
          _stack.pop_back();
          uint64_t a1 = _f.a1;
          const inner &a2 = *_f.a2;
          _stack.emplace_back(
              _after_double_inner_in_INode_2{a1, std::move(_result)});
          _stack.emplace_back(_call{_f.a2});
        } else {
          auto _f =
              std::move(std::get<_after_double_inner_in_INode_2>(_popped));
          _stack.pop_back();
          uint64_t a1 = _f.a1;
          _result = inner::inode(std::move(_f._tmp2), (a1 * UINT64_C(2)),
                                 std::move(_result));
        }
      }
      return _result;
    }

    uint64_t inner_sum() const {
      const inner *_self = this;

      // Explicit stack replaces the non-tail recursion of inner_sum: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const inner *_self;
      };

      struct _after_inner_sum_in_INode {
        uint64_t a1;
        const inner *a2;
      };

      struct _after_inner_sum_in_INode_2 {
        uint64_t a1;
        uint64_t _tmp2;
      };

      using _frame = std::variant<_call, _after_inner_sum_in_INode,
                                  _after_inner_sum_in_INode_2>;
      uint64_t _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const inner *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename inner::ILeaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2] = std::get<typename inner::INode>(_sv.v());
            _stack.emplace_back(_after_inner_sum_in_INode{a1, crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_inner_sum_in_INode>(_popped)) {
          auto _f = std::move(std::get<_after_inner_sum_in_INode>(_popped));
          _stack.pop_back();
          uint64_t a1 = _f.a1;
          const inner &a2 = *_f.a2;
          _stack.emplace_back(
              _after_inner_sum_in_INode_2{a1, std::move(_result)});
          _stack.emplace_back(_call{_f.a2});
        } else {
          auto _f = std::move(std::get<_after_inner_sum_in_INode_2>(_popped));
          _stack.pop_back();
          uint64_t a1 = _f.a1;
          _result = ((_f._tmp2 + a1) + std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1> T1 inner_rec(T1 f, F1 &&f0) const {
      return this->template inner_rect<T1>(std::move(f), f0);
    }

    template <typename T1, typename F1> T1 inner_rect(T1 f, F1 &&f0) const {
      const inner *_self = this;

      // Explicit stack replaces the non-tail recursion of inner_rect: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const inner *_self;
      };

      struct _after_inner_rect_in_INode {
        std::shared_ptr<inner> a0;
        uint64_t a1;
        const inner *a2;
      };

      struct _after_inner_rect_in_INode_2 {
        std::shared_ptr<inner> a0;
        uint64_t a1;
        const inner *a2;
        T1 _tmp2;
      };

      using _frame = std::variant<_call, _after_inner_rect_in_INode,
                                  _after_inner_rect_in_INode_2>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const inner *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename inner::ILeaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2] = std::get<typename inner::INode>(_sv.v());
            _stack.emplace_back(
                _after_inner_rect_in_INode{a0, a1, crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_inner_rect_in_INode>(_popped)) {
          auto _f = std::move(std::get<_after_inner_rect_in_INode>(_popped));
          _stack.pop_back();
          std::shared_ptr<inner> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          const inner &a2 = *_f.a2;
          _stack.emplace_back(_after_inner_rect_in_INode_2{
              std::move(a0), a1, &a2, std::move(_result)});
          _stack.emplace_back(_call{_f.a2});
        } else {
          auto _f = std::move(std::get<_after_inner_rect_in_INode_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<inner> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          const inner &a2 = *_f.a2;
          _result = f0(*a0, std::move(_f._tmp2), a1, a2, std::move(_result));
        }
      }
      return _result;
    }
  };

  /// An outer tree type with an inner tree as a non-recursive field.
  struct outer {
    // TYPES
    struct OLeaf {};

    struct ONode {
      std::shared_ptr<outer> a0;
      inner a1;
      std::shared_ptr<outer> a2;
    };

    using variant_t = std::variant<OLeaf, ONode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    outer() {}

    explicit outer(OLeaf _v) : v_(_v) {}

    explicit outer(ONode _v) : v_(std::move(_v)) {}

    static outer oleaf() { return outer(OLeaf{}); }

    static outer onode(outer a0, inner a1, outer a2) {
      return outer(ONode{std::make_shared<outer>(std::move(a0)), std::move(a1),
                         std::make_shared<outer>(std::move(a2))});
    }

    // MANIPULATORS
    ~outer() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<OLeaf>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<ONode>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a2 && _alt->a2.use_count() == 1))) {
          return;
        }
      }
      crane::small_vector<std::shared_ptr<outer>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<ONode>(&_v)) {
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

    outer(const outer &) = default;
    outer &operator=(const outer &) = default;
    outer(outer &&) = default;
    outer &operator=(outer &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// TEST 6: Dup outer tree — use outer value twice.
    std::pair<outer, outer> dup_outer() const {
      return std::make_pair(*this, *this);
    }

    outer transform_outer() const {
      const outer *_self = this;

      // Explicit stack replaces the non-tail recursion of transform_outer:
      // _call frames are pending calls, _after frames resume a caller.
      struct _call {
        const outer *_self;
      };

      struct _after_transform_outer_in_ONode {
        inner a1;
        const outer *a2;
      };

      struct _after_transform_outer_in_ONode_2 {
        inner a1;
        outer _tmp2;
      };

      using _frame = std::variant<_call, _after_transform_outer_in_ONode,
                                  _after_transform_outer_in_ONode_2>;
      outer _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const outer *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename outer::OLeaf>(_sv.v())) {
            _result = outer::oleaf();
          } else {
            const auto &[a0, a1, a2] = std::get<typename outer::ONode>(_sv.v());
            _stack.emplace_back(
                _after_transform_outer_in_ONode{a1, crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_transform_outer_in_ONode>(
                       _popped)) {
          auto _f =
              std::move(std::get<_after_transform_outer_in_ONode>(_popped));
          _stack.pop_back();
          inner a1 = std::move(_f.a1);
          const outer &a2 = *_f.a2;
          _stack.emplace_back(_after_transform_outer_in_ONode_2{
              std::move(a1), std::move(_result)});
          _stack.emplace_back(_call{_f.a2});
        } else {
          auto _f =
              std::move(std::get<_after_transform_outer_in_ONode_2>(_popped));
          _stack.pop_back();
          inner a1 = std::move(_f.a1);
          _result = outer::onode(std::move(_f._tmp2), a1.double_inner(),
                                 std::move(_result));
        }
      }
      return _result;
    }

    uint64_t outer_sum() const {
      const outer *_self = this;

      // Explicit stack replaces the non-tail recursion of outer_sum: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const outer *_self;
      };

      struct _after_outer_sum_in_ONode {
        inner a1;
        const outer *a2;
      };

      struct _after_outer_sum_in_ONode_2 {
        inner a1;
        uint64_t _tmp2;
      };

      using _frame = std::variant<_call, _after_outer_sum_in_ONode,
                                  _after_outer_sum_in_ONode_2>;
      uint64_t _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const outer *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename outer::OLeaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2] = std::get<typename outer::ONode>(_sv.v());
            _stack.emplace_back(_after_outer_sum_in_ONode{a1, crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_outer_sum_in_ONode>(_popped)) {
          auto _f = std::move(std::get<_after_outer_sum_in_ONode>(_popped));
          _stack.pop_back();
          inner a1 = std::move(_f.a1);
          const outer &a2 = *_f.a2;
          _stack.emplace_back(
              _after_outer_sum_in_ONode_2{std::move(a1), std::move(_result)});
          _stack.emplace_back(_call{_f.a2});
        } else {
          auto _f = std::move(std::get<_after_outer_sum_in_ONode_2>(_popped));
          _stack.pop_back();
          inner a1 = std::move(_f.a1);
          _result = ((_f._tmp2 + a1.inner_sum()) + std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1> T1 outer_rec(T1 f, F1 &&f0) const {
      return this->template outer_rect<T1>(std::move(f), f0);
    }

    template <typename T1, typename F1> T1 outer_rect(T1 f, F1 &&f0) const {
      const outer *_self = this;

      // Explicit stack replaces the non-tail recursion of outer_rect: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const outer *_self;
      };

      struct _after_outer_rect_in_ONode {
        std::shared_ptr<outer> a0;
        inner a1;
        const outer *a2;
      };

      struct _after_outer_rect_in_ONode_2 {
        std::shared_ptr<outer> a0;
        inner a1;
        const outer *a2;
        T1 _tmp2;
      };

      using _frame = std::variant<_call, _after_outer_rect_in_ONode,
                                  _after_outer_rect_in_ONode_2>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const outer *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename outer::OLeaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2] = std::get<typename outer::ONode>(_sv.v());
            _stack.emplace_back(
                _after_outer_rect_in_ONode{a0, a1, crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_outer_rect_in_ONode>(_popped)) {
          auto _f = std::move(std::get<_after_outer_rect_in_ONode>(_popped));
          _stack.pop_back();
          std::shared_ptr<outer> a0 = std::move(_f.a0);
          inner a1 = std::move(_f.a1);
          const outer &a2 = *_f.a2;
          _stack.emplace_back(_after_outer_rect_in_ONode_2{
              std::move(a0), std::move(a1), &a2, std::move(_result)});
          _stack.emplace_back(_call{_f.a2});
        } else {
          auto _f = std::move(std::get<_after_outer_rect_in_ONode_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<outer> a0 = std::move(_f.a0);
          inner a1 = std::move(_f.a1);
          const outer &a2 = *_f.a2;
          _result = f0(*a0, std::move(_f._tmp2), a1, a2, std::move(_result));
        }
      }
      return _result;
    }
  };

  /// An expression type with varying constructor arities.
  struct expr {
    // TYPES
    struct Lit {
      uint64_t a0;
    };

    struct Neg {
      std::shared_ptr<expr> a0;
    };

    struct Add {
      std::shared_ptr<expr> a0;
      std::shared_ptr<expr> a1;
    };

    struct Mul {
      std::shared_ptr<expr> a0;
      std::shared_ptr<expr> a1;
    };

    using variant_t = std::variant<Lit, Neg, Add, Mul>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    expr() {}

    explicit expr(Lit _v) : v_(std::move(_v)) {}

    explicit expr(Neg _v) : v_(std::move(_v)) {}

    explicit expr(Add _v) : v_(std::move(_v)) {}

    explicit expr(Mul _v) : v_(std::move(_v)) {}

    static expr lit(uint64_t a0) { return expr(Lit{a0}); }

    static expr neg(expr a0) {
      return expr(Neg{std::make_shared<expr>(std::move(a0))});
    }

    static expr add(expr a0, expr a1) {
      return expr(Add{std::make_shared<expr>(std::move(a0)),
                      std::make_shared<expr>(std::move(a1))});
    }

    static expr mul(expr a0, expr a1) {
      return expr(Mul{std::make_shared<expr>(std::move(a0)),
                      std::make_shared<expr>(std::move(a1))});
    }

    // MANIPULATORS
    ~expr() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<Lit>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<Neg>(&v_mut())) {
        if (!(_alt->a0 && _alt->a0.use_count() == 1)) {
          return;
        }
      }
      if (auto *_alt = std::get_if<Add>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a1 && _alt->a1.use_count() == 1))) {
          return;
        }
      }
      if (auto *_alt = std::get_if<Mul>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a1 && _alt->a1.use_count() == 1))) {
          return;
        }
      }
      crane::small_vector<std::shared_ptr<expr>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Neg>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
        }
        if (auto *_alt = std::get_if<Add>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
        if (auto *_alt = std::get_if<Mul>(&_v)) {
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

    expr(const expr &) = default;
    expr &operator=(const expr &) = default;
    expr(expr &&) = default;
    expr &operator=(expr &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// TEST 8: Mixed operations — build outer from expr eval results,
    /// then transform. Cross-type interaction.
    inner expr_to_inner() const {
      const expr *_self = this;

      // Explicit stack replaces the non-tail recursion of expr_to_inner: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const expr *_self;
      };

      struct _after_expr_to_inner_in_Add {
        const expr *a1;
      };

      struct _after_expr_to_inner_in_Add_2 {
        inner _tmp2;
      };

      struct _after_expr_to_inner_in_Mul {
        const expr *a1;
      };

      struct _after_expr_to_inner_in_Mul_2 {
        inner _tmp4;
      };

      using _frame = std::variant<
          _call, _after_expr_to_inner_in_Add, _after_expr_to_inner_in_Add_2,
          _after_expr_to_inner_in_Mul, _after_expr_to_inner_in_Mul_2>;
      inner _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Lit>(_sv.v());
            _result = inner::inode(inner::ileaf(), a0, inner::ileaf());
          } else if (std::holds_alternative<typename expr::Neg>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Neg>(_sv.v());
            _stack.emplace_back(_call{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_after_expr_to_inner_in_Add{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else {
            const auto &[a0, a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_after_expr_to_inner_in_Mul{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_expr_to_inner_in_Add>(_popped)) {
          auto _f = std::move(std::get<_after_expr_to_inner_in_Add>(_popped));
          _stack.pop_back();
          const expr &a1 = *_f.a1;
          _stack.emplace_back(_after_expr_to_inner_in_Add_2{std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else if (
                std::holds_alternative<_after_expr_to_inner_in_Add_2>(_popped)) {
          auto _f = std::move(std::get<_after_expr_to_inner_in_Add_2>(_popped));
          _stack.pop_back();
          _result = inner::inode(std::move(_f._tmp2), UINT64_C(0),
                                 std::move(_result));
        } else if (std::holds_alternative<_after_expr_to_inner_in_Mul>(_popped)) {
          auto _f = std::move(std::get<_after_expr_to_inner_in_Mul>(_popped));
          _stack.pop_back();
          const expr &a1 = *_f.a1;
          _stack.emplace_back(_after_expr_to_inner_in_Mul_2{std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else {
          auto _f = std::move(std::get<_after_expr_to_inner_in_Mul_2>(_popped));
          _stack.pop_back();
          _result = inner::inode(std::move(_f._tmp4), UINT64_C(1),
                                 std::move(_result));
        }
      }
      return _result;
    }

    /// TEST 7: Map over expr tree — rebuild with transformed values.
    expr double_expr() const {
      const expr *_self = this;

      // Explicit stack replaces the non-tail recursion of double_expr: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const expr *_self;
      };

      struct _after_double_expr_in_Add {
        const expr *a1;
      };

      struct _after_double_expr_in_Add_2 {
        expr _tmp3;
      };

      struct _after_double_expr_in_Mul {
        const expr *a1;
      };

      struct _after_double_expr_in_Mul_2 {
        expr _tmp5;
      };

      struct _after_double_expr_in_Neg {};

      using _frame =
          std::variant<_call, _after_double_expr_in_Add,
                       _after_double_expr_in_Add_2, _after_double_expr_in_Mul,
                       _after_double_expr_in_Mul_2, _after_double_expr_in_Neg>;
      expr _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Lit>(_sv.v());
            _result = expr::lit((a0 * UINT64_C(2)));
          } else if (std::holds_alternative<typename expr::Neg>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Neg>(_sv.v());
            _stack.emplace_back(_after_double_expr_in_Neg{});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_after_double_expr_in_Add{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else {
            const auto &[a0, a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_after_double_expr_in_Mul{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_double_expr_in_Add>(_popped)) {
          auto _f = std::move(std::get<_after_double_expr_in_Add>(_popped));
          _stack.pop_back();
          const expr &a1 = *_f.a1;
          _stack.emplace_back(_after_double_expr_in_Add_2{std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else if (std::holds_alternative<_after_double_expr_in_Add_2>(_popped)) {
          auto _f = std::move(std::get<_after_double_expr_in_Add_2>(_popped));
          _stack.pop_back();
          _result = expr::add(std::move(_f._tmp3), std::move(_result));
        } else if (std::holds_alternative<_after_double_expr_in_Mul>(_popped)) {
          auto _f = std::move(std::get<_after_double_expr_in_Mul>(_popped));
          _stack.pop_back();
          const expr &a1 = *_f.a1;
          _stack.emplace_back(_after_double_expr_in_Mul_2{std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else if (std::holds_alternative<_after_double_expr_in_Mul_2>(_popped)) {
          auto _f = std::move(std::get<_after_double_expr_in_Mul_2>(_popped));
          _stack.pop_back();
          _result = expr::mul(std::move(_f._tmp5), std::move(_result));
        } else {
          auto _f = std::move(std::get<_after_double_expr_in_Neg>(_popped));
          _stack.pop_back();
          _result = expr::neg(std::move(_result));
        }
      }
      return _result;
    }

    uint64_t eval_expr() const {
      const expr *_self = this;

      // Explicit stack replaces the non-tail recursion of eval_expr: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const expr *_self;
      };

      struct _after_eval_expr_in_Add {
        const expr *a1;
      };

      struct _after_eval_expr_in_Add_2 {
        uint64_t _tmp2;
      };

      struct _after_eval_expr_in_Mul {
        const expr *a1;
      };

      struct _after_eval_expr_in_Mul_2 {
        uint64_t _tmp4;
      };

      using _frame = std::variant<
          _call, _after_eval_expr_in_Add, _after_eval_expr_in_Add_2,
          _after_eval_expr_in_Mul, _after_eval_expr_in_Mul_2>;
      uint64_t _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Lit>(_sv.v());
            _result = std::move(a0);
          } else if (std::holds_alternative<typename expr::Neg>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Neg>(_sv.v());
            _stack.emplace_back(_call{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_after_eval_expr_in_Add{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else {
            const auto &[a0, a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_after_eval_expr_in_Mul{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_eval_expr_in_Add>(_popped)) {
          auto _f = std::move(std::get<_after_eval_expr_in_Add>(_popped));
          _stack.pop_back();
          const expr &a1 = *_f.a1;
          _stack.emplace_back(_after_eval_expr_in_Add_2{std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else if (std::holds_alternative<_after_eval_expr_in_Add_2>(_popped)) {
          auto _f = std::move(std::get<_after_eval_expr_in_Add_2>(_popped));
          _stack.pop_back();
          _result = (_f._tmp2 + std::move(_result));
        } else if (std::holds_alternative<_after_eval_expr_in_Mul>(_popped)) {
          auto _f = std::move(std::get<_after_eval_expr_in_Mul>(_popped));
          _stack.pop_back();
          const expr &a1 = *_f.a1;
          _stack.emplace_back(_after_eval_expr_in_Mul_2{std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else {
          auto _f = std::move(std::get<_after_eval_expr_in_Mul_2>(_popped));
          _stack.pop_back();
          _result = (_f._tmp4 * std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1, typename F2, typename F3>
    T1 expr_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2) const {
      return this->template expr_rect<T1>(f, f0, f1, f2);
    }

    template <typename T1, typename F0, typename F1, typename F2, typename F3>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
    T1 expr_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2) const {
      const expr *_self = this;

      // Explicit stack replaces the non-tail recursion of expr_rect: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const expr *_self;
      };

      struct _after_expr_rect_in_Add {
        std::shared_ptr<expr> a0;
        const expr *a1;
      };

      struct _after_expr_rect_in_Add_2 {
        std::shared_ptr<expr> a0;
        const expr *a1;
        T1 _tmp3;
      };

      struct _after_expr_rect_in_Mul {
        std::shared_ptr<expr> a0;
        const expr *a1;
      };

      struct _after_expr_rect_in_Mul_2 {
        std::shared_ptr<expr> a0;
        const expr *a1;
        T1 _tmp5;
      };

      struct _after_expr_rect_in_Neg {
        std::shared_ptr<expr> a0;
      };

      using _frame =
          std::variant<_call, _after_expr_rect_in_Add,
                       _after_expr_rect_in_Add_2, _after_expr_rect_in_Mul,
                       _after_expr_rect_in_Mul_2, _after_expr_rect_in_Neg>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Lit>(_sv.v());
            _result = f(a0);
          } else if (std::holds_alternative<typename expr::Neg>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Neg>(_sv.v());
            _stack.emplace_back(_after_expr_rect_in_Neg{a0});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_after_expr_rect_in_Add{a0, crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else {
            const auto &[a0, a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_after_expr_rect_in_Mul{a0, crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_expr_rect_in_Add>(_popped)) {
          auto _f = std::move(std::get<_after_expr_rect_in_Add>(_popped));
          _stack.pop_back();
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          const expr &a1 = *_f.a1;
          _stack.emplace_back(
              _after_expr_rect_in_Add_2{std::move(a0), &a1,
                                        std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else if (std::holds_alternative<_after_expr_rect_in_Add_2>(_popped)) {
          auto _f = std::move(std::get<_after_expr_rect_in_Add_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          const expr &a1 = *_f.a1;
          _result = f1(*a0, std::move(_f._tmp3), a1, std::move(_result));
        } else if (std::holds_alternative<_after_expr_rect_in_Mul>(_popped)) {
          auto _f = std::move(std::get<_after_expr_rect_in_Mul>(_popped));
          _stack.pop_back();
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          const expr &a1 = *_f.a1;
          _stack.emplace_back(
              _after_expr_rect_in_Mul_2{std::move(a0), &a1,
                                        std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else if (std::holds_alternative<_after_expr_rect_in_Mul_2>(_popped)) {
          auto _f = std::move(std::get<_after_expr_rect_in_Mul_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          const expr &a1 = *_f.a1;
          _result = f2(*a0, std::move(_f._tmp5), a1, std::move(_result));
        } else {
          auto _f = std::move(std::get<_after_expr_rect_in_Neg>(_popped));
          _stack.pop_back();
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          _result = f0(*a0, std::move(_result));
        }
      }
      return _result;
    }
  };

  /// A three-child tree.
  struct tree3 {
    // TYPES
    struct T3Leaf {};

    struct T3Node {
      std::shared_ptr<tree3> a0;
      std::shared_ptr<tree3> a1;
      std::shared_ptr<tree3> a2;
      uint64_t a3;
    };

    using variant_t = std::variant<T3Leaf, T3Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree3() {}

    explicit tree3(T3Leaf _v) : v_(_v) {}

    explicit tree3(T3Node _v) : v_(std::move(_v)) {}

    static tree3 t3leaf() { return tree3(T3Leaf{}); }

    static tree3 t3node(tree3 a0, tree3 a1, tree3 a2, uint64_t a3) {
      return tree3(T3Node{std::make_shared<tree3>(std::move(a0)),
                          std::make_shared<tree3>(std::move(a1)),
                          std::make_shared<tree3>(std::move(a2)), a3});
    }

    // MANIPULATORS
    ~tree3() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<T3Leaf>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<T3Node>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a1 && _alt->a1.use_count() == 1) ||
              (_alt->a2 && _alt->a2.use_count() == 1))) {
          return;
        }
      }
      crane::small_vector<std::shared_ptr<tree3>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<T3Node>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            _stack.push_back(std::move(_alt->a1));
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

    tree3(const tree3 &) = default;
    tree3 &operator=(const tree3 &) = default;
    tree3(tree3 &&) = default;
    tree3 &operator=(tree3 &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t tree3_sum() const {
      const tree3 *_self = this;

      // Explicit stack replaces the non-tail recursion of tree3_sum: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const tree3 *_self;
      };

      struct _after_tree3_sum_in_T3Node {
        const tree3 *a1;
        const tree3 *a2;
        uint64_t a3;
      };

      struct _after_tree3_sum_in_T3Node_2 {
        const tree3 *a2;
        uint64_t a3;
        uint64_t _tmp3;
      };

      struct _after_tree3_sum_in_T3Node_3 {
        uint64_t a3;
        uint64_t _tmp3;
        uint64_t _tmp2;
      };

      using _frame = std::variant<_call, _after_tree3_sum_in_T3Node,
                                  _after_tree3_sum_in_T3Node_2,
                                  _after_tree3_sum_in_T3Node_3>;
      uint64_t _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const tree3 *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree3::T3Leaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename tree3::T3Node>(_sv.v());
            _stack.emplace_back(
                _after_tree3_sum_in_T3Node{crane_raw(a1), crane_raw(a2), a3});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_tree3_sum_in_T3Node>(_popped)) {
          auto _f = std::move(std::get<_after_tree3_sum_in_T3Node>(_popped));
          _stack.pop_back();
          const tree3 &a1 = *_f.a1;
          const tree3 &a2 = *_f.a2;
          uint64_t a3 = _f.a3;
          _stack.emplace_back(
              _after_tree3_sum_in_T3Node_2{&a2, a3, std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else if (
                std::holds_alternative<_after_tree3_sum_in_T3Node_2>(_popped)) {
          auto _f = std::move(std::get<_after_tree3_sum_in_T3Node_2>(_popped));
          _stack.pop_back();
          const tree3 &a2 = *_f.a2;
          uint64_t a3 = _f.a3;
          _stack.emplace_back(
              _after_tree3_sum_in_T3Node_3{a3, _f._tmp3, std::move(_result)});
          _stack.emplace_back(_call{_f.a2});
        } else {
          auto _f = std::move(std::get<_after_tree3_sum_in_T3Node_3>(_popped));
          _stack.pop_back();
          uint64_t a3 = _f.a3;
          _result = (((_f._tmp3 + _f._tmp2) + std::move(_result)) + a3);
        }
      }
      return _result;
    }

    template <typename T1, typename F1> T1 tree3_rec(T1 f, F1 &&f0) const {
      return this->template tree3_rect<T1>(std::move(f), f0);
    }

    template <typename T1, typename F1> T1 tree3_rect(T1 f, F1 &&f0) const {
      const tree3 *_self = this;

      // Explicit stack replaces the non-tail recursion of tree3_rect: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const tree3 *_self;
      };

      struct _after_tree3_rect_in_T3Node {
        std::shared_ptr<tree3> a0;
        const tree3 *a1;
        const tree3 *a2;
        uint64_t a3;
      };

      struct _after_tree3_rect_in_T3Node_2 {
        std::shared_ptr<tree3> a0;
        const tree3 *a1;
        const tree3 *a2;
        uint64_t a3;
        T1 _tmp3;
      };

      struct _after_tree3_rect_in_T3Node_3 {
        std::shared_ptr<tree3> a0;
        const tree3 *a1;
        const tree3 *a2;
        uint64_t a3;
        T1 _tmp3;
        T1 _tmp2;
      };

      using _frame = std::variant<_call, _after_tree3_rect_in_T3Node,
                                  _after_tree3_rect_in_T3Node_2,
                                  _after_tree3_rect_in_T3Node_3>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const tree3 *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree3::T3Leaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename tree3::T3Node>(_sv.v());
            _stack.emplace_back(_after_tree3_rect_in_T3Node{a0, crane_raw(a1),
                                                            crane_raw(a2), a3});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_tree3_rect_in_T3Node>(_popped)) {
          auto _f = std::move(std::get<_after_tree3_rect_in_T3Node>(_popped));
          _stack.pop_back();
          std::shared_ptr<tree3> a0 = std::move(_f.a0);
          const tree3 &a1 = *_f.a1;
          const tree3 &a2 = *_f.a2;
          uint64_t a3 = _f.a3;
          _stack.emplace_back(_after_tree3_rect_in_T3Node_2{
              std::move(a0), &a1, &a2, a3, std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else if (
                std::holds_alternative<_after_tree3_rect_in_T3Node_2>(_popped)) {
          auto _f = std::move(std::get<_after_tree3_rect_in_T3Node_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<tree3> a0 = std::move(_f.a0);
          const tree3 &a1 = *_f.a1;
          const tree3 &a2 = *_f.a2;
          uint64_t a3 = _f.a3;
          _stack.emplace_back(_after_tree3_rect_in_T3Node_3{
              std::move(a0), &a1, &a2, a3, std::move(_f._tmp3),
              std::move(_result)});
          _stack.emplace_back(_call{_f.a2});
        } else {
          auto _f = std::move(std::get<_after_tree3_rect_in_T3Node_3>(_popped));
          _stack.pop_back();
          std::shared_ptr<tree3> a0 = std::move(_f.a0);
          const tree3 &a1 = *_f.a1;
          const tree3 &a2 = *_f.a2;
          uint64_t a3 = _f.a3;
          _result = f0(*a0, std::move(_f._tmp3), a1, std::move(_f._tmp2), a2,
                       std::move(_result), a3);
        }
      }
      return _result;
    }
  };

  /// TEST 1: Build and sum an outer tree with inner tree values.
  /// Tests nested value-type clone/destructor interaction.
  static inline const uint64_t test_outer_basic = []() {
    outer o = outer::onode(
        outer::onode(outer::oleaf(),
                     inner::inode(inner::ileaf(), UINT64_C(10), inner::ileaf()),
                     outer::oleaf()),
        inner::inode(inner::inode(inner::ileaf(), UINT64_C(1), inner::ileaf()),
                     UINT64_C(2),
                     inner::inode(inner::ileaf(), UINT64_C(3), inner::ileaf())),
        outer::onode(outer::oleaf(),
                     inner::inode(inner::ileaf(), UINT64_C(20), inner::ileaf()),
                     outer::oleaf()));
    return o.outer_sum();
  }();
  /// TEST 2: Dup pattern — use inner tree twice in outer construction.
  static outer dup_inner(const inner &i);
  static inline const uint64_t test_dup_inner = []() {
    inner i = inner::inode(
        inner::inode(inner::ileaf(), UINT64_C(5), inner::ileaf()), UINT64_C(10),
        inner::inode(inner::ileaf(), UINT64_C(15), inner::ileaf()));
    return dup_inner(std::move(i)).outer_sum();
  }();
  static inline const uint64_t test_transform = []() {
    outer o =
        outer::onode(outer::oleaf(),
                     inner::inode(inner::ileaf(), UINT64_C(5), inner::ileaf()),
                     outer::onode(outer::oleaf(),
                                  inner::inode(inner::ileaf(), UINT64_C(10),
                                               inner::ileaf()),
                                  outer::oleaf()));
    return o.transform_outer().outer_sum();
  }();
  /// TEST 4: Build and evaluate a complex expression tree.
  static inline const uint64_t test_expr = []() {
    expr e = expr::add(
        expr::mul(expr::add(expr::lit(UINT64_C(2)), expr::lit(UINT64_C(3))),
                  expr::lit(UINT64_C(4))),
        expr::neg(expr::add(expr::lit(UINT64_C(10)), expr::lit(UINT64_C(5)))));
    return e.eval_expr();
  }();
  /// TEST 5: Deep 3-child tree to stress clone/destructor.
  static tree3 build_tree3(uint64_t n);
  static inline const uint64_t test_tree3 =
      build_tree3(UINT64_C(4)).tree3_sum();
  static inline const uint64_t test_dup_outer = []() {
    outer o =
        outer::onode(outer::oleaf(),
                     inner::inode(inner::ileaf(), UINT64_C(42), inner::ileaf()),
                     outer::oleaf());
    std::pair<outer, outer> p = o.dup_outer();
    return (std::move(p).first.outer_sum() + std::move(p).second.outer_sum());
  }();
  static inline const uint64_t test_double_expr =
      expr::add(expr::lit(UINT64_C(5)),
                expr::mul(expr::lit(UINT64_C(3)),
                          expr::lit(UINT64_C(7))))
          .double_expr().eval_expr();
  static inline const uint64_t test_cross_type = []() {
    expr e =
        expr::add(expr::lit(UINT64_C(5)),
                  expr::mul(expr::lit(UINT64_C(3)), expr::lit(UINT64_C(7))));
    inner i = e.expr_to_inner();
    outer o = outer::onode(outer::oleaf(), i, outer::oleaf());
    return (o.outer_sum() + i.inner_sum());
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE29
