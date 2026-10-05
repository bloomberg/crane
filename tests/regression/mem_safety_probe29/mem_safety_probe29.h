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

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const inner *_self;
      };

      /// CraneCont_INode: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_INode {
        uint64_t a1;
        std::shared_ptr<inner> a2;
      };

      /// CraneCont_INode_1: saves [_tmp2, a1], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_INode_1 {
        inner _tmp2;
        uint64_t a1;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_INode, CraneCont_INode_1>;
      inner _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified double_inner: CraneEnter -> CraneCont_INode ->
      /// CraneCont_INode_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const inner *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename inner::ILeaf>(_sv.v())) {
            _result = inner::ileaf();
          } else {
            const auto &[a0, a1, a2] = std::get<typename inner::INode>(_sv.v());
            _stack.emplace_back(CraneCont_INode{a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_INode>(_frame)) {
          auto _f = std::move(std::get<CraneCont_INode>(_frame));
          uint64_t a1 = _f.a1;
          std::shared_ptr<inner> a2 = std::move(_f.a2);
          _stack.emplace_back(CraneCont_INode_1{std::move(_result), a1});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<CraneCont_INode_1>(_frame));
          uint64_t a1 = _f.a1;
          _result = inner::inode(std::move(_f._tmp2), (a1 * UINT64_C(2)),
                                 std::move(_result));
        }
      }
      return _result;
    }

    uint64_t inner_sum() const {
      const inner *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const inner *_self;
      };

      /// CraneCont_INode: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_INode {
        uint64_t a1;
        std::shared_ptr<inner> a2;
      };

      /// CraneCont_INode_1: saves [_tmp2, a1], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_INode_1 {
        uint64_t _tmp2;
        uint64_t a1;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_INode, CraneCont_INode_1>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified inner_sum: CraneEnter -> CraneCont_INode ->
      /// CraneCont_INode_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const inner *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename inner::ILeaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2] = std::get<typename inner::INode>(_sv.v());
            _stack.emplace_back(CraneCont_INode{a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_INode>(_frame)) {
          auto _f = std::move(std::get<CraneCont_INode>(_frame));
          uint64_t a1 = _f.a1;
          std::shared_ptr<inner> a2 = std::move(_f.a2);
          _stack.emplace_back(CraneCont_INode_1{std::move(_result), a1});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<CraneCont_INode_1>(_frame));
          uint64_t a1 = _f.a1;
          _result = ((_f._tmp2 + a1) + std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
    T1 inner_rec(const T1 &f, F1 &&f0) const {
      return this->template inner_rect<T1>(f, f0);
    }

    template <typename T1, typename F1> T1 inner_rect(T1 f, F1 &&f0) const {
      const inner *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const inner *_self;
      };

      /// CraneCont_INode: saves [a0, a1, a2], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_INode {
        std::shared_ptr<inner> a0;
        uint64_t a1;
        std::shared_ptr<inner> a2;
      };

      /// CraneCont_INode_1: saves [_tmp2, a0, a1, a2], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_INode_1 {
        T1 _tmp2;
        std::shared_ptr<inner> a0;
        uint64_t a1;
        std::shared_ptr<inner> a2;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_INode, CraneCont_INode_1>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified inner_rect: CraneEnter -> CraneCont_INode ->
      /// CraneCont_INode_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const inner *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename inner::ILeaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2] = std::get<typename inner::INode>(_sv.v());
            _stack.emplace_back(CraneCont_INode{a0, a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_INode>(_frame)) {
          auto _f = std::move(std::get<CraneCont_INode>(_frame));
          std::shared_ptr<inner> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          std::shared_ptr<inner> a2 = std::move(_f.a2);
          _stack.emplace_back(
              CraneCont_INode_1{std::move(_result), std::move(a0), a1, a2});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<CraneCont_INode_1>(_frame));
          std::shared_ptr<inner> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          std::shared_ptr<inner> a2 = std::move(_f.a2);
          _result = f0(*a0, std::move(_f._tmp2), a1, *a2, std::move(_result));
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

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const outer *_self;
      };

      /// CraneCont_ONode: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_ONode {
        inner a1;
        std::shared_ptr<outer> a2;
      };

      /// CraneCont_ONode_1: saves [_tmp2, a1], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_ONode_1 {
        outer _tmp2;
        inner a1;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_ONode, CraneCont_ONode_1>;
      outer _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified transform_outer: CraneEnter -> CraneCont_ONode ->
      /// CraneCont_ONode_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const outer *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename outer::OLeaf>(_sv.v())) {
            _result = outer::oleaf();
          } else {
            const auto &[a0, a1, a2] = std::get<typename outer::ONode>(_sv.v());
            _stack.emplace_back(CraneCont_ONode{a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_ONode>(_frame)) {
          auto _f = std::move(std::get<CraneCont_ONode>(_frame));
          inner a1 = std::move(_f.a1);
          std::shared_ptr<outer> a2 = std::move(_f.a2);
          _stack.emplace_back(
              CraneCont_ONode_1{std::move(_result), std::move(a1)});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<CraneCont_ONode_1>(_frame));
          inner a1 = std::move(_f.a1);
          _result = outer::onode(std::move(_f._tmp2), a1.double_inner(),
                                 std::move(_result));
        }
      }
      return _result;
    }

    uint64_t outer_sum() const {
      const outer *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const outer *_self;
      };

      /// CraneCont_ONode: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_ONode {
        inner a1;
        std::shared_ptr<outer> a2;
      };

      /// CraneCont_ONode_1: saves [_tmp2, a1], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_ONode_1 {
        uint64_t _tmp2;
        inner a1;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_ONode, CraneCont_ONode_1>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified outer_sum: CraneEnter -> CraneCont_ONode ->
      /// CraneCont_ONode_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const outer *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename outer::OLeaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2] = std::get<typename outer::ONode>(_sv.v());
            _stack.emplace_back(CraneCont_ONode{a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_ONode>(_frame)) {
          auto _f = std::move(std::get<CraneCont_ONode>(_frame));
          inner a1 = std::move(_f.a1);
          std::shared_ptr<outer> a2 = std::move(_f.a2);
          _stack.emplace_back(
              CraneCont_ONode_1{std::move(_result), std::move(a1)});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<CraneCont_ONode_1>(_frame));
          inner a1 = std::move(_f.a1);
          _result = ((_f._tmp2 + a1.inner_sum()) + std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
    T1 outer_rec(const T1 &f, F1 &&f0) const {
      return this->template outer_rect<T1>(f, f0);
    }

    template <typename T1, typename F1> T1 outer_rect(T1 f, F1 &&f0) const {
      const outer *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const outer *_self;
      };

      /// CraneCont_ONode: saves [a0, a1, a2], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_ONode {
        std::shared_ptr<outer> a0;
        inner a1;
        std::shared_ptr<outer> a2;
      };

      /// CraneCont_ONode_1: saves [_tmp2, a0, a1, a2], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_ONode_1 {
        T1 _tmp2;
        std::shared_ptr<outer> a0;
        inner a1;
        std::shared_ptr<outer> a2;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_ONode, CraneCont_ONode_1>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified outer_rect: CraneEnter -> CraneCont_ONode ->
      /// CraneCont_ONode_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const outer *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename outer::OLeaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2] = std::get<typename outer::ONode>(_sv.v());
            _stack.emplace_back(CraneCont_ONode{a0, a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_ONode>(_frame)) {
          auto _f = std::move(std::get<CraneCont_ONode>(_frame));
          std::shared_ptr<outer> a0 = std::move(_f.a0);
          inner a1 = std::move(_f.a1);
          std::shared_ptr<outer> a2 = std::move(_f.a2);
          _stack.emplace_back(CraneCont_ONode_1{
              std::move(_result), std::move(a0), std::move(a1), a2});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<CraneCont_ONode_1>(_frame));
          std::shared_ptr<outer> a0 = std::move(_f.a0);
          inner a1 = std::move(_f.a1);
          std::shared_ptr<outer> a2 = std::move(_f.a2);
          _result = f0(*a0, std::move(_f._tmp2), a1, *a2, std::move(_result));
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

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const expr *_self;
      };

      /// CraneCont_Add: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Add {
        std::shared_ptr<expr> a1;
      };

      /// CraneCont_Add_1: saves [_tmp2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Add_1 {
        inner _tmp2;
      };

      /// CraneCont_Mul: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Mul {
        std::shared_ptr<expr> a1;
      };

      /// CraneCont_Mul_1: saves [_tmp4], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Mul_1 {
        inner _tmp4;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Add, CraneCont_Add_1,
                       CraneCont_Mul, CraneCont_Mul_1>;
      inner _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified expr_to_inner: CraneEnter -> CraneCont_Add ->
      /// CraneCont_Add_1 -> CraneCont_Mul -> CraneCont_Mul_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Lit>(_sv.v());
            _result = inner::inode(inner::ileaf(), a0, inner::ileaf());
          } else if (std::holds_alternative<typename expr::Neg>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Neg>(_sv.v());
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(CraneCont_Add{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else {
            const auto &[a0, a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(CraneCont_Mul{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Add>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Add>(_frame));
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_Add_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_Add_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Add_1>(_frame));
          _result = inner::inode(std::move(_f._tmp2), UINT64_C(0),
                                 std::move(_result));
        } else if (std::holds_alternative<CraneCont_Mul>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Mul>(_frame));
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_Mul_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<CraneCont_Mul_1>(_frame));
          _result = inner::inode(std::move(_f._tmp4), UINT64_C(1),
                                 std::move(_result));
        }
      }
      return _result;
    }

    /// TEST 7: Map over expr tree — rebuild with transformed values.
    expr double_expr() const {
      const expr *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const expr *_self;
      };

      /// CraneCont_Add: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Add {
        std::shared_ptr<expr> a1;
      };

      /// CraneCont_Add_1: saves [_tmp3], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Add_1 {
        expr _tmp3;
      };

      /// CraneCont_Mul: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Mul {
        std::shared_ptr<expr> a1;
      };

      /// CraneCont_Mul_1: saves [_tmp5], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Mul_1 {
        expr _tmp5;
      };

      /// CraneCont_Neg: resumes after recursive call, then processes rest.
      struct CraneCont_Neg {};

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Add, CraneCont_Add_1,
                       CraneCont_Mul, CraneCont_Mul_1, CraneCont_Neg>;
      expr _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified double_expr: CraneEnter -> CraneCont_Add -> CraneCont_Add_1
      /// -> CraneCont_Mul -> CraneCont_Mul_1 -> CraneCont_Neg.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Lit>(_sv.v());
            _result = expr::lit((a0 * UINT64_C(2)));
          } else if (std::holds_alternative<typename expr::Neg>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Neg>(_sv.v());
            _stack.emplace_back(CraneCont_Neg{});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(CraneCont_Add{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else {
            const auto &[a0, a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(CraneCont_Mul{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Add>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Add>(_frame));
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_Add_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_Add_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Add_1>(_frame));
          _result = expr::add(std::move(_f._tmp3), std::move(_result));
        } else if (std::holds_alternative<CraneCont_Mul>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Mul>(_frame));
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_Mul_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_Mul_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Mul_1>(_frame));
          _result = expr::mul(std::move(_f._tmp5), std::move(_result));
        } else {
          auto _f = std::move(std::get<CraneCont_Neg>(_frame));
          _result = expr::neg(std::move(_result));
        }
      }
      return _result;
    }

    uint64_t eval_expr() const {
      const expr *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const expr *_self;
      };

      /// CraneCont_Add: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Add {
        std::shared_ptr<expr> a1;
      };

      /// CraneCont_Add_1: saves [_tmp2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Add_1 {
        uint64_t _tmp2;
      };

      /// CraneCont_Mul: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Mul {
        std::shared_ptr<expr> a1;
      };

      /// CraneCont_Mul_1: saves [_tmp4], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Mul_1 {
        uint64_t _tmp4;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Add, CraneCont_Add_1,
                       CraneCont_Mul, CraneCont_Mul_1>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified eval_expr: CraneEnter -> CraneCont_Add -> CraneCont_Add_1 ->
      /// CraneCont_Mul -> CraneCont_Mul_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Lit>(_sv.v());
            _result = std::move(a0);
          } else if (std::holds_alternative<typename expr::Neg>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Neg>(_sv.v());
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(CraneCont_Add{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else {
            const auto &[a0, a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(CraneCont_Mul{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Add>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Add>(_frame));
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_Add_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_Add_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Add_1>(_frame));
          _result = (_f._tmp2 + std::move(_result));
        } else if (std::holds_alternative<CraneCont_Mul>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Mul>(_frame));
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_Mul_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<CraneCont_Mul_1>(_frame));
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

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const expr *_self;
      };

      /// CraneCont_Add: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Add {
        std::shared_ptr<expr> a0;
        std::shared_ptr<expr> a1;
      };

      /// CraneCont_Add_1: saves [_tmp3, a0, a1], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Add_1 {
        T1 _tmp3;
        std::shared_ptr<expr> a0;
        std::shared_ptr<expr> a1;
      };

      /// CraneCont_Mul: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Mul {
        std::shared_ptr<expr> a0;
        std::shared_ptr<expr> a1;
      };

      /// CraneCont_Mul_1: saves [_tmp5, a0, a1], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Mul_1 {
        T1 _tmp5;
        std::shared_ptr<expr> a0;
        std::shared_ptr<expr> a1;
      };

      /// CraneCont_Neg: saves [a0], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Neg {
        std::shared_ptr<expr> a0;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Add, CraneCont_Add_1,
                       CraneCont_Mul, CraneCont_Mul_1, CraneCont_Neg>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified expr_rect: CraneEnter -> CraneCont_Add -> CraneCont_Add_1 ->
      /// CraneCont_Mul -> CraneCont_Mul_1 -> CraneCont_Neg.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Lit>(_sv.v());
            _result = f(a0);
          } else if (std::holds_alternative<typename expr::Neg>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Neg>(_sv.v());
            _stack.emplace_back(CraneCont_Neg{a0});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(CraneCont_Add{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          } else {
            const auto &[a0, a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(CraneCont_Mul{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Add>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Add>(_frame));
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          _stack.emplace_back(
              CraneCont_Add_1{std::move(_result), std::move(a0), a1});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_Add_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Add_1>(_frame));
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          _result = f1(*a0, std::move(_f._tmp3), *a1, std::move(_result));
        } else if (std::holds_alternative<CraneCont_Mul>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Mul>(_frame));
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          _stack.emplace_back(
              CraneCont_Mul_1{std::move(_result), std::move(a0), a1});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_Mul_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Mul_1>(_frame));
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          _result = f2(*a0, std::move(_f._tmp5), *a1, std::move(_result));
        } else {
          auto _f = std::move(std::get<CraneCont_Neg>(_frame));
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

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const tree3 *_self;
      };

      /// CraneCont_T3Node: saves [a1, a2, a3], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_T3Node {
        std::shared_ptr<tree3> a1;
        std::shared_ptr<tree3> a2;
        uint64_t a3;
      };

      /// CraneCont_T3Node_1: saves [_tmp3, a2, a3], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_T3Node_1 {
        uint64_t _tmp3;
        std::shared_ptr<tree3> a2;
        uint64_t a3;
      };

      /// CraneCont_T3Node_2: saves [_tmp2, _tmp3, a3], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_T3Node_2 {
        uint64_t _tmp2;
        uint64_t _tmp3;
        uint64_t a3;
      };

      using CraneFrame = std::variant<CraneEnter, CraneCont_T3Node,
                                      CraneCont_T3Node_1, CraneCont_T3Node_2>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified tree3_sum: CraneEnter -> CraneCont_T3Node ->
      /// CraneCont_T3Node_1 -> CraneCont_T3Node_2.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const tree3 *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree3::T3Leaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename tree3::T3Node>(_sv.v());
            _stack.emplace_back(CraneCont_T3Node{a1, a2, a3});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_T3Node>(_frame)) {
          auto _f = std::move(std::get<CraneCont_T3Node>(_frame));
          std::shared_ptr<tree3> a1 = std::move(_f.a1);
          std::shared_ptr<tree3> a2 = std::move(_f.a2);
          uint64_t a3 = _f.a3;
          _stack.emplace_back(
              CraneCont_T3Node_1{std::move(_result), std::move(a2), a3});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_T3Node_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_T3Node_1>(_frame));
          std::shared_ptr<tree3> a2 = std::move(_f.a2);
          uint64_t a3 = _f.a3;
          _stack.emplace_back(
              CraneCont_T3Node_2{std::move(_result), _f._tmp3, a3});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<CraneCont_T3Node_2>(_frame));
          uint64_t a3 = _f.a3;
          _result = (((_f._tmp3 + _f._tmp2) + std::move(_result)) + a3);
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
    T1 tree3_rec(const T1 &f, F1 &&f0) const {
      return this->template tree3_rect<T1>(f, f0);
    }

    template <typename T1, typename F1> T1 tree3_rect(T1 f, F1 &&f0) const {
      const tree3 *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const tree3 *_self;
      };

      /// CraneCont_T3Node: saves [a0, a1, a2, a3], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_T3Node {
        std::shared_ptr<tree3> a0;
        std::shared_ptr<tree3> a1;
        std::shared_ptr<tree3> a2;
        uint64_t a3;
      };

      /// CraneCont_T3Node_1: saves [_tmp3, a0, a1, a2, a3], resumes after
      /// recursive call, then processes rest.
      struct CraneCont_T3Node_1 {
        T1 _tmp3;
        std::shared_ptr<tree3> a0;
        std::shared_ptr<tree3> a1;
        std::shared_ptr<tree3> a2;
        uint64_t a3;
      };

      /// CraneCont_T3Node_2: saves [_tmp2, _tmp3, a0, a1, a2, a3], resumes
      /// after recursive call, then processes rest.
      struct CraneCont_T3Node_2 {
        T1 _tmp2;
        T1 _tmp3;
        std::shared_ptr<tree3> a0;
        std::shared_ptr<tree3> a1;
        std::shared_ptr<tree3> a2;
        uint64_t a3;
      };

      using CraneFrame = std::variant<CraneEnter, CraneCont_T3Node,
                                      CraneCont_T3Node_1, CraneCont_T3Node_2>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified tree3_rect: CraneEnter -> CraneCont_T3Node ->
      /// CraneCont_T3Node_1 -> CraneCont_T3Node_2.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const tree3 *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree3::T3Leaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename tree3::T3Node>(_sv.v());
            _stack.emplace_back(CraneCont_T3Node{a0, a1, a2, a3});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_T3Node>(_frame)) {
          auto _f = std::move(std::get<CraneCont_T3Node>(_frame));
          std::shared_ptr<tree3> a0 = std::move(_f.a0);
          std::shared_ptr<tree3> a1 = std::move(_f.a1);
          std::shared_ptr<tree3> a2 = std::move(_f.a2);
          uint64_t a3 = _f.a3;
          _stack.emplace_back(CraneCont_T3Node_1{
              std::move(_result), std::move(a0), a1, std::move(a2), a3});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_T3Node_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_T3Node_1>(_frame));
          std::shared_ptr<tree3> a0 = std::move(_f.a0);
          std::shared_ptr<tree3> a1 = std::move(_f.a1);
          std::shared_ptr<tree3> a2 = std::move(_f.a2);
          uint64_t a3 = _f.a3;
          _stack.emplace_back(
              CraneCont_T3Node_2{std::move(_result), std::move(_f._tmp3),
                                 std::move(a0), std::move(a1), a2, a3});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<CraneCont_T3Node_2>(_frame));
          std::shared_ptr<tree3> a0 = std::move(_f.a0);
          std::shared_ptr<tree3> a1 = std::move(_f.a1);
          std::shared_ptr<tree3> a2 = std::move(_f.a2);
          uint64_t a3 = _f.a3;
          _result = f0(*a0, std::move(_f._tmp3), *a1, std::move(_f._tmp2), *a2,
                       std::move(_result), a3);
        }
      }
      return _result;
    }
  };

  /// TEST 1: Build and sum an outer tree with inner tree values.
  /// Tests nested value-type clone/destructor interaction.
  static constexpr uint64_t test_outer_basic = UINT64_C(36);
  /// TEST 2: Dup pattern — use inner tree twice in outer construction.
  static outer dup_inner(const inner &i);
  static constexpr uint64_t test_dup_inner = UINT64_C(90);
  static constexpr uint64_t test_transform = UINT64_C(30);
  /// TEST 4: Build and evaluate a complex expression tree.
  static constexpr uint64_t test_expr = UINT64_C(35);
  /// TEST 5: Deep 3-child tree to stress clone/destructor.
  static tree3 build_tree3(uint64_t n);
  static constexpr uint64_t test_tree3 = UINT64_C(58);
  static inline const uint64_t test_dup_outer = []() {
    outer o =
        outer::onode(outer::oleaf(),
                     inner::inode(inner::ileaf(), UINT64_C(42), inner::ileaf()),
                     outer::oleaf());
    std::pair<outer, outer> p = std::move(o).dup_outer();
    return (p.first.outer_sum() + p.second.outer_sum());
  }();
  static constexpr uint64_t test_double_expr = UINT64_C(94);
  static constexpr uint64_t test_cross_type = UINT64_C(32);
};

#endif // INCLUDED_MEM_SAFETY_PROBE29
