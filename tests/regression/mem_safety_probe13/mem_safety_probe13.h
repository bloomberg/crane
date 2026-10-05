#ifndef INCLUDED_MEM_SAFETY_PROBE13
#define INCLUDED_MEM_SAFETY_PROBE13

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct MemSafetyProbe13 {
  /// Probe 13: Value-type move semantics and the flatten optimization.
  ///
  /// The flatten optimization (make_owned_param_matches +
  /// optimize_frame_push_args) marks match branches as owned and
  /// moves unique_ptr child fields into Enter frames. If a closure
  /// or continuation simultaneously references the same field,
  /// the move creates use-after-move.
  ///
  /// Also tests: closures returned from functions that take
  /// value-type parameters, and deep pattern match nesting
  /// with closures at each level.
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

    /// TEST 3: Function that matches twice on same tree.
    /// First match extracts subtrees, second match on a subtree
    /// creates a closure capturing the other subtree.
    uint64_t double_match() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        const tree &a0_value = *a0;
        const tree &a2_value = *a2;
        if (std::holds_alternative<typename tree::Leaf>(a0_value.v())) {
          return (a2_value.tree_sum() + a1);
        } else {
          const auto &[a00, a10, a20] =
              std::get<typename tree::Node>(a0_value.v());
          const tree &a00_value = *a00;
          const tree &a20_value = *a20;
          crane::fn<uint64_t(uint64_t)> f = [=](uint64_t n) {
            return ((a2_value.tree_sum() + a20_value.tree_sum()) + n);
          };
          return (f(a10) + a00_value.tree_sum());
        }
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

    template <typename T1, typename F1>
    T1 tree_rec(const T1 &f, F1 &&f0) const {
      return this->template tree_rect<T1>(f, f0);
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

  template <typename A> struct mylist {
    // TYPES
    struct Mynil {};

    struct Mycons {
      A a0;
      std::shared_ptr<mylist<A>> a1;
    };

    using variant_t = std::variant<Mynil, Mycons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    mylist() {}

    explicit mylist(Mynil _v) : v_(_v) {}

    explicit mylist(Mycons _v) : v_(std::move(_v)) {}

    template <typename CraneU>
    mylist(const mylist<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename mylist<CraneU>::Mynil>(
                    _other.v())) {
              return Mynil{};
            } else {
              const auto &[a0, a1] =
                  std::get<typename mylist<CraneU>::Mycons>(_other.v());
              return Mycons{
                  [&]() -> A {
                    if constexpr (crane_convertible<A, const CraneU &>) {
                      return crane_convert<A>(a0);
                    } else {
                      throw std::logic_error(
                          "unreachable: inactive constructor field at this "
                          "instantiation");
                    }
                  }(),
                  (a1 ? std::make_shared<mylist<A>>(
                            crane_convert<mylist<A>>(*a1))
                      : nullptr)};
            }
          }()) {}

    static mylist<A> mynil() { return mylist<A>(Mynil{}); }

    static mylist<A> mycons(A a0, mylist<A> a1) {
      return mylist<A>(
          Mycons{std::move(a0), std::make_shared<mylist<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~mylist() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<mylist<A>> {
        if (auto *_alt = std::get_if<Mycons>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a1);
          }
        }
        return nullptr;
      };
      std::shared_ptr<mylist<A>> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    mylist(const mylist &) = default;
    mylist &operator=(const mylist &) = default;
    mylist(mylist &&) = default;
    mylist &operator=(mylist &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    mylist<A> app(mylist<A> l2) const {
      std::optional<mylist<A>> _root{};
      std::shared_ptr<mylist<A>> *_write = nullptr;
      const mylist<A> *_loop_self = this;
      mylist<A> _loop_l2 = std::move(l2);
      while (true) {
        auto &&_sv = *_loop_self;
        if (std::holds_alternative<typename mylist<A>::Mynil>(_sv.v())) {
          auto _value = std::move(_loop_l2);
          (_write ? *(*_write = std::make_shared<mylist<A>>(std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(_sv.v());
          auto _cell = typename mylist<A>::Mycons(a0, nullptr);
          mylist<A> &_node =
              (_write
                   ? *(*_write = std::make_shared<mylist<A>>(std::move(_cell)))
                   : _root.emplace(std::move(_cell)));
          _write = &std::get<typename mylist<A>::Mycons>(_node.v_mut()).a1;
          _loop_self = crane_raw(a1);
          continue;
        }
      }
      return std::move(*_root);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, const A &>
    mylist<T1> map_list(F0 &&f) const {
      std::optional<mylist<T1>> _root{};
      std::shared_ptr<mylist<T1>> *_write = nullptr;
      const mylist<A> *_loop_self = this;
      while (true) {
        auto &&_sv = *_loop_self;
        if (std::holds_alternative<typename mylist<A>::Mynil>(_sv.v())) {
          auto _value = mylist<T1>::mynil();
          (_write ? *(*_write = std::make_shared<mylist<T1>>(std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(_sv.v());
          auto _cell = typename mylist<T1>::Mycons(f(a0), nullptr);
          mylist<T1> &_node =
              (_write
                   ? *(*_write = std::make_shared<mylist<T1>>(std::move(_cell)))
                   : _root.emplace(std::move(_cell)));
          _write = &std::get<typename mylist<T1>::Mycons>(_node.v_mut()).a1;
          _loop_self = crane_raw(a1);
          continue;
        }
      }
      return std::move(*_root);
    }

    uint64_t length() const {
      auto go_impl = [](auto &_self_go, const mylist<A> &l0,
                        uint64_t acc) -> uint64_t {
        if (std::holds_alternative<typename mylist<A>::Mynil>(l0.v())) {
          return acc;
        } else {
          const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(l0.v());
          return _self_go(_self_go, *a1, (acc + UINT64_C(1)));
        }
      };
      {
        const mylist<A> &_lc1_l0 = *this;
        uint64_t _lc1_acc = UINT64_C(0);
        return go_impl(go_impl, _lc1_l0, _lc1_acc);
      }
    }

    template <typename T1, typename F1>
    T1 mylist_rec(const T1 &f, F1 &&f0) const {
      return this->template mylist_rect<T1>(f, f0);
    }

    template <typename T1, typename F1> T1 mylist_rect(T1 f, F1 &&f0) const {
      const mylist<A> *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const mylist<A> *_self;
      };

      /// CraneCont_Mycons: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Mycons {
        A a0;
        std::shared_ptr<mylist<A>> a1;
      };

      using CraneFrame = std::variant<CraneEnter, CraneCont_Mycons>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified mylist_rect: CraneEnter -> CraneCont_Mycons.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const mylist<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename mylist<A>::Mynil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] =
                std::get<typename mylist<A>::Mycons>(_sv.v());
            _stack.emplace_back(CraneCont_Mycons{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<CraneCont_Mycons>(_frame));
          auto a0 = std::move(_f.a0);
          std::shared_ptr<mylist<A>> a1 = std::move(_f.a1);
          _result = f0(a0, *a1, std::move(_result));
        }
      }
      return _result;
    }
  };

  static uint64_t sum_list(const mylist<uint64_t> &l);
  /// TEST 1: Double-recursion on tree where both subtrees
  /// are used in closures AND in recursive calls.
  /// Tests if the flatten optimization moves unique_ptr fields
  /// that are also captured by closures.
  static std::pair<mylist<uint64_t>, mylist<crane::fn<uint64_t(uint64_t)>>>
  tree_vals_and_fns(const tree &t);
  static constexpr uint64_t test_vals_and_fns = UINT64_C(35);
  static constexpr uint64_t test_double_match = UINT64_C(26);
  /// TEST 4: Deeply nested tree with closures at EVERY level.
  /// Each closure captures values from its level AND from the parent.
  /// Tests stack depth and closure lifetime with deep nesting.
  static tree make_deep(uint64_t n);
  static mylist<crane::fn<uint64_t(uint64_t)>> depth_fns(const tree &t,
                                                         uint64_t parent_val);
  static constexpr uint64_t test_depth_fns = UINT64_C(29);

  /// TEST 5: Transform a tree by replacing each value with a
  /// function, then evaluate. Tests closures in recursive
  /// tree transformation.
  struct ftree {
    // TYPES
    struct FLeaf {};

    struct FNode {
      std::shared_ptr<ftree> a0;
      crane::fn<uint64_t(uint64_t)> a1;
      std::shared_ptr<ftree> a2;
    };

    using variant_t = std::variant<FLeaf, FNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    ftree() {}

    explicit ftree(FLeaf _v) : v_(_v) {}

    explicit ftree(FNode _v) : v_(std::move(_v)) {}

    static ftree fleaf() { return ftree(FLeaf{}); }

    static ftree fnode(ftree a0, crane::fn<uint64_t(uint64_t)> a1, ftree a2) {
      return ftree(FNode{std::make_shared<ftree>(std::move(a0)), std::move(a1),
                         std::make_shared<ftree>(std::move(a2))});
    }

    // MANIPULATORS
    ~ftree() {
      crane::small_vector<std::shared_ptr<ftree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<FNode>(&_v)) {
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

    ftree(const ftree &) = default;
    ftree &operator=(const ftree &) = default;
    ftree(ftree &&) = default;
    ftree &operator=(ftree &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t eval_ftree(uint64_t base) const {
      const ftree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const ftree *_self;
      };

      /// CraneCont_FNode: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_FNode {
        crane::fn<uint64_t(uint64_t)> a1;
        std::shared_ptr<ftree> a2;
      };

      /// CraneCont_FNode_1: saves [_tmp2, a1], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_FNode_1 {
        uint64_t _tmp2;
        crane::fn<uint64_t(uint64_t)> a1;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_FNode, CraneCont_FNode_1>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified eval_ftree: CraneEnter -> CraneCont_FNode ->
      /// CraneCont_FNode_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const ftree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ftree::FLeaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2] = std::get<typename ftree::FNode>(_sv.v());
            _stack.emplace_back(CraneCont_FNode{a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_FNode>(_frame)) {
          auto _f = std::move(std::get<CraneCont_FNode>(_frame));
          crane::fn<uint64_t(uint64_t)> a1 = std::move(_f.a1);
          std::shared_ptr<ftree> a2 = std::move(_f.a2);
          _stack.emplace_back(
              CraneCont_FNode_1{std::move(_result), std::move(a1)});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<CraneCont_FNode_1>(_frame));
          crane::fn<uint64_t(uint64_t)> a1 = std::move(_f.a1);
          _result = ((_f._tmp2 + a1(base)) + std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
    T1 ftree_rec(const T1 &f, F1 &&f0) const {
      return this->template ftree_rect<T1>(f, f0);
    }

    template <typename T1, typename F1> T1 ftree_rect(T1 f, F1 &&f0) const {
      const ftree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const ftree *_self;
      };

      /// CraneCont_FNode: saves [a0, a1, a2], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_FNode {
        std::shared_ptr<ftree> a0;
        crane::fn<uint64_t(uint64_t)> a1;
        std::shared_ptr<ftree> a2;
      };

      /// CraneCont_FNode_1: saves [_tmp2, a0, a1, a2], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_FNode_1 {
        T1 _tmp2;
        std::shared_ptr<ftree> a0;
        crane::fn<uint64_t(uint64_t)> a1;
        std::shared_ptr<ftree> a2;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_FNode, CraneCont_FNode_1>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified ftree_rect: CraneEnter -> CraneCont_FNode ->
      /// CraneCont_FNode_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const ftree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ftree::FLeaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2] = std::get<typename ftree::FNode>(_sv.v());
            _stack.emplace_back(CraneCont_FNode{a0, a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_FNode>(_frame)) {
          auto _f = std::move(std::get<CraneCont_FNode>(_frame));
          std::shared_ptr<ftree> a0 = std::move(_f.a0);
          crane::fn<uint64_t(uint64_t)> a1 = std::move(_f.a1);
          std::shared_ptr<ftree> a2 = std::move(_f.a2);
          _stack.emplace_back(CraneCont_FNode_1{
              std::move(_result), std::move(a0), std::move(a1), a2});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<CraneCont_FNode_1>(_frame));
          std::shared_ptr<ftree> a0 = std::move(_f.a0);
          crane::fn<uint64_t(uint64_t)> a1 = std::move(_f.a1);
          std::shared_ptr<ftree> a2 = std::move(_f.a2);
          _result = f0(*a0, std::move(_f._tmp2), a1, *a2, std::move(_result));
        }
      }
      return _result;
    }
  };

  static ftree tree_to_ftree(const tree &t);
  static constexpr uint64_t test_ftree = UINT64_C(321);
  /// TEST 6: Flatten a tree of lists into a single list,
  /// where each list element is a closure.
  static mylist<crane::fn<uint64_t(uint64_t)>> flatten_tree_fns(const tree &t);
  static constexpr uint64_t test_flatten_fns = UINT64_C(24);
};

#endif // INCLUDED_MEM_SAFETY_PROBE13
