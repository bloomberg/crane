#ifndef INCLUDED_ACCUM_CLOSURE_CAPTURE
#define INCLUDED_ACCUM_CLOSURE_CAPTURE

#include "crane_fn.h"
#include "fn.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <utility>
#include <variant>

struct AccumClosureCapture {
  /// Define fn_list BEFORE tree so fn_list is not a forward inductive.
  /// This lets extract_closures (tree -> fn_list) be methodified on tree,
  /// because fn_list in the return type is not blocked by forward-ref check.
  struct fn_list {
    // TYPES
    struct FNil {};

    struct FCons {
      crane::fn<uint64_t(uint64_t)> a0;
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

    static fn_list fcons(crane::fn<uint64_t(uint64_t)> a0, fn_list a1) {
      return fn_list(
          FCons{std::move(a0), std::make_shared<fn_list>(std::move(a1))});
    }

    // MANIPULATORS
    ~fn_list() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<fn_list> {
        if (auto *_alt = std::get_if<FCons>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a1);
          }
        }
        return nullptr;
      };
      std::shared_ptr<fn_list> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    fn_list(const fn_list &) = default;
    fn_list &operator=(const fn_list &) = default;
    fn_list(fn_list &&) = default;
    fn_list &operator=(fn_list &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t apply_all(uint64_t init) const {
      const fn_list *_loop_self = this;
      uint64_t _loop_init = std::move(init);
      while (true) {
        auto &&_sv = *_loop_self;
        if (std::holds_alternative<typename fn_list::FNil>(_sv.v())) {
          return _loop_init;
        } else {
          const auto &[a0, a1] = std::get<typename fn_list::FCons>(_sv.v());
          _loop_self = crane_raw(a1);
          _loop_init = a0(_loop_init);
        }
      }
    }

    template <typename T1, typename F1> T1 fn_list_rec(T1 f, F1 &&f0) const {
      const fn_list *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const fn_list *_self;
      };

      /// CraneCont_FCons: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_FCons {
        crane::fn<uint64_t(uint64_t)> a0;
        std::shared_ptr<fn_list> a1;
      };

      using CraneFrame = std::variant<CraneEnter, CraneCont_FCons>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified fn_list_rec: CraneEnter -> CraneCont_FCons.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const fn_list *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename fn_list::FNil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] = std::get<typename fn_list::FCons>(_sv.v());
            _stack.emplace_back(CraneCont_FCons{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<CraneCont_FCons>(_frame));
          crane::fn<uint64_t(uint64_t)> a0 = std::move(_f.a0);
          std::shared_ptr<fn_list> a1 = std::move(_f.a1);
          _result = f0(a0, *a1, std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1> T1 fn_list_rect(T1 f, F1 &&f0) const {
      const fn_list *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const fn_list *_self;
      };

      /// CraneCont_FCons: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_FCons {
        crane::fn<uint64_t(uint64_t)> a0;
        std::shared_ptr<fn_list> a1;
      };

      using CraneFrame = std::variant<CraneEnter, CraneCont_FCons>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified fn_list_rect: CraneEnter -> CraneCont_FCons.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const fn_list *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename fn_list::FNil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] = std::get<typename fn_list::FCons>(_sv.v());
            _stack.emplace_back(CraneCont_FCons{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<CraneCont_FCons>(_frame));
          crane::fn<uint64_t(uint64_t)> a0 = std::move(_f.a0);
          std::shared_ptr<fn_list> a1 = std::move(_f.a1);
          _result = f0(a0, *a1, std::move(_result));
        }
      }
      return _result;
    }
  };

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
    tree(tree &&) = default;
    tree &operator=(tree &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// BUG HYPOTHESIS: extract_closures is methodified on tree. The closures
    /// capture this (for tree_sum t) as a raw pointer. They are stored in
    /// fn_list. After extract_closures returns, the temporary tree is
    /// destroyed. Calling the closures from apply_all dereferences dangling
    /// this.
    fn_list extract_closures() const {
      tree _self_val = *this;
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return fn_list::fnil();
      } else {
        auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return fn_list::fcons(
            [=](uint64_t x) { return (x + _self_val.tree_sum()); },
            fn_list::fcons(
                [=](uint64_t x) { return (x + a1); },
                fn_list::fcons(
                    [=](uint64_t x) { return (x + _self_val.tree_sum()); },
                    fn_list::fnil())));
      }
    }

    uint64_t tree_sum() const {
      const tree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const tree *_self;
      };

      /// CraneCont_Node: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Node {
        uint64_t a1;
        std::shared_ptr<tree> a2;
      };

      /// CraneCont_Node_1: saves [_tmp2, a1], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Node_1 {
        uint64_t _tmp2;
        uint64_t a1;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified tree_sum: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(CraneCont_Node{a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Node>(_frame));
          uint64_t a1 = _f.a1;
          std::shared_ptr<tree> a2 = std::move(_f.a2);
          _stack.emplace_back(CraneCont_Node_1{std::move(_result), a1});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
          uint64_t a1 = _f.a1;
          _result = ((_f._tmp2 + a1) + std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1> T1 tree_rec(T1 f, F1 &&f0) const {
      const tree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const tree *_self;
      };

      /// CraneCont_Node: saves [a0, a1, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Node {
        std::shared_ptr<tree> a0;
        uint64_t a1;
        std::shared_ptr<tree> a2;
      };

      /// CraneCont_Node_1: saves [_tmp2, a0, a1, a2], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_Node_1 {
        T1 _tmp2;
        std::shared_ptr<tree> a0;
        uint64_t a1;
        std::shared_ptr<tree> a2;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified tree_rec: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(CraneCont_Node{a0, a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Node>(_frame));
          std::shared_ptr<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          std::shared_ptr<tree> a2 = std::move(_f.a2);
          _stack.emplace_back(
              CraneCont_Node_1{std::move(_result), std::move(a0), a1, a2});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
          std::shared_ptr<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          std::shared_ptr<tree> a2 = std::move(_f.a2);
          _result = f0(*a0, std::move(_f._tmp2), a1, *a2, std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1> T1 tree_rect(T1 f, F1 &&f0) const {
      const tree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const tree *_self;
      };

      /// CraneCont_Node: saves [a0, a1, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Node {
        std::shared_ptr<tree> a0;
        uint64_t a1;
        std::shared_ptr<tree> a2;
      };

      /// CraneCont_Node_1: saves [_tmp2, a0, a1, a2], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_Node_1 {
        T1 _tmp2;
        std::shared_ptr<tree> a0;
        uint64_t a1;
        std::shared_ptr<tree> a2;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified tree_rect: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(CraneCont_Node{a0, a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Node>(_frame));
          std::shared_ptr<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          std::shared_ptr<tree> a2 = std::move(_f.a2);
          _stack.emplace_back(
              CraneCont_Node_1{std::move(_result), std::move(a0), a1, a2});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
          std::shared_ptr<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          std::shared_ptr<tree> a2 = std::move(_f.a2);
          _result = f0(*a0, std::move(_f._tmp2), a1, *a2, std::move(_result));
        }
      }
      return _result;
    }
  };

  /// test1: Create tree with sum=42, extract closures, apply to 0.
  /// Expected: 0 + 42 = 42, 42 + 20 = 62, 62 + 42 = 104.
  /// With dangling this, tree_sum reads garbage.
  static inline const uint64_t test1 = []() {
    fn_list fs =
        tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                   UINT64_C(20),
                   tree::node(tree::leaf(), UINT64_C(12), tree::leaf()))
            .extract_closures();
    return std::move(fs).apply_all(UINT64_C(0));
  }();
  /// test2: Allocate a noise tree between extracting closures and applying
  /// them. Increases memory pressure on freed region.
  static inline const uint64_t test2 = []() {
    fn_list fs = tree::node(tree::leaf(), UINT64_C(100), tree::leaf())
                     .extract_closures();
    uint64_t noise =
        tree::node(tree::leaf(), UINT64_C(999), tree::leaf()).tree_sum();
    return std::move(fs).apply_all(noise);
  }();
};

#endif // INCLUDED_ACCUM_CLOSURE_CAPTURE
