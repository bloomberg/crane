#ifndef INCLUDED_MEM_SAFETY_PROBE3
#define INCLUDED_MEM_SAFETY_PROBE3

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

struct MemSafetyProbe3 {
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

    /// TEST 9: Closure stored in option alongside tree data in pair.
    std::pair<std::optional<crane::fn<uint64_t(uint64_t)>>, tree>
    opt_pair(bool b) const {
      tree _self_val = *this;
      return std::make_pair(
          (b ? std::make_optional<crane::fn<uint64_t(uint64_t)>>(
                   [=](uint64_t _x0) -> uint64_t {
                     return std::move(_self_val).sum_values(_x0);
                   })
             : std::optional<crane::fn<uint64_t(uint64_t)>>()),
          *this);
    }

    /// TEST 8: Three closures, each capturing different tree,
    /// applied in a specific order with results feeding forward.
    uint64_t chain_three(tree t2, const tree &t3) const {
      crane::fn<uint64_t(uint64_t)> f1 = [&](uint64_t _x0) -> uint64_t {
        return std::move(*this).sum_values(_x0);
      };
      crane::fn<uint64_t(uint64_t)> f2 = [&](uint64_t _x0) -> uint64_t {
        return std::move(t2).sum_values(_x0);
      };
      return t3.sum_values(f2(f1(UINT64_C(0))));
    }

    /// TEST 7: Map a tree, producing a new tree. Then sum the new tree.
    /// The mapped function captures a tree value.
    template <typename F0>
      requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
    tree map_tree(F0 &&f) const {
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
        tree _tmp2;
        uint64_t a1;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
      tree _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified map_tree: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = tree::leaf();
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
          _result = tree::node(std::move(_f._tmp2), f(a1), std::move(_result));
        }
      }
      return _result;
    }

    /// TEST 6: Nested pair: pair of pairs of closures.
    std::pair<
        std::pair<crane::fn<uint64_t(uint64_t)>, crane::fn<uint64_t(uint64_t)>>,
        uint64_t>
    nested_pair() const {
      tree _self_val = *this;
      return std::make_pair(std::make_pair(
                                [=](uint64_t _x0) -> uint64_t {
                                  return _self_val.sum_values(_x0);
                                },
                                [](uint64_t x) { return x; }),
                            this->sum_values(UINT64_C(0)));
    }

    /// TEST 5: Mutual use: tree used BOTH as partial application arg
    /// AND as match scrutinee in the SAME scope.
    uint64_t mutual_use() const {
      tree _self_val = *this;
      crane::fn<uint64_t(uint64_t)> f = [=](uint64_t _x0) -> uint64_t {
        return _self_val.sum_values(_x0);
      };
      uint64_t r = [&]() {
        if (std::holds_alternative<typename tree::Leaf>(this->v())) {
          return UINT64_C(0);
        } else {
          auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
          return a1;
        }
      }();
      return f(r);
    }

    /// TEST 4: Tree traversal that builds up a nat accumulator
    /// using local fixpoint. The tree is captured in the fixpoint scope.
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

    /// TEST 3: Partial application result stored in a pair, then both
    /// elements of the pair are applied. The pair construction must
    /// properly clone the closures.
    std::pair<crane::fn<uint64_t(uint64_t)>, crane::fn<uint64_t(uint64_t)>>
    paired_closures(tree t2) const {
      tree _self_val = *this;
      return std::make_pair(
          [=](uint64_t _x0) -> uint64_t {
            return std::move(_self_val).sum_values(_x0);
          },
          [=](uint64_t _x0) -> uint64_t {
            return std::move(t2).sum_values(_x0);
          });
    }

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

  /// TEST 1: Local fixpoint capturing a tree value.
  /// The fixpoint accesses the captured tree on each recursive call.
  static constexpr uint64_t local_fix_capture = UINT64_C(171);
  /// TEST 2: Local fixpoint returning a closure that captures
  /// a match-destructured field from a tree.
  static constexpr uint64_t fix_with_closure = UINT64_C(80);
  static inline const uint64_t test_paired_closures = []() {
    tree t1 = tree::node(tree::leaf(), UINT64_C(10), tree::leaf());
    tree t2 = tree::node(tree::leaf(), UINT64_C(20), tree::leaf());
    std::pair<crane::fn<uint64_t(uint64_t)>, crane::fn<uint64_t(uint64_t)>> p =
        std::move(t1).paired_closures(std::move(t2));
    return (p.first(UINT64_C(5)) + p.second(UINT64_C(5)));
  }();
  static constexpr uint64_t test_tree_sum = UINT64_C(60);
  /// f = sum_values (Node (Node Leaf 10 Leaf) 20 (...))
  /// r = 20. f 20 = 10+30+20+20 = 80
  static constexpr uint64_t test_mutual_use = UINT64_C(80);
  static inline const uint64_t test_nested_pair = []() {
    tree t = tree::node(tree::leaf(), UINT64_C(42), tree::leaf());
    std::pair<
        std::pair<crane::fn<uint64_t(uint64_t)>, crane::fn<uint64_t(uint64_t)>>,
        uint64_t>
        p = std::move(t).nested_pair();
    return (((p.first).first(UINT64_C(10)) + (p.first).second(UINT64_C(10))) +
            p.second);
  }();
  static constexpr uint64_t test_map_with_captured = UINT64_C(330);
  static constexpr uint64_t test_chain_three = UINT64_C(60);
  static inline const uint64_t test_opt_pair = []() {
    tree t = tree::node(tree::leaf(), UINT64_C(42), tree::leaf());
    std::pair<std::optional<crane::fn<uint64_t(uint64_t)>>, tree> p =
        std::move(t).opt_pair(true);
    auto _cs = p.first;
    if (_cs.has_value()) {
      const crane::fn<uint64_t(uint64_t)> &f = *_cs;
      return (f(UINT64_C(10)) + std::move(p).second.sum_values(UINT64_C(0)));
    } else {
      return UINT64_C(0);
    }
  }();
  /// TEST 10: Large tree with deep recursion — stresses the
  /// loopified tree traversal and clone mechanisms.
  static tree build_deep(uint64_t n);
  static inline const uint64_t test_deep_tree = []() {
    tree t = build_deep(UINT64_C(100));
    return std::move(t).tree_sum();
  }();

  /// TEST 11: Fixpoint that takes a function argument and uses it
  /// alongside captured tree data.
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &&>
  static uint64_t
  apply_n_times(F0 &&f, uint64_t n,
                uint64_t x) { /// CraneEnter: captures varying parameters for
                              /// each recursive call.

    struct CraneEnter {
      uint64_t n;
    };

    /// CraneCont_n_: resumes after recursive call, then processes rest.
    struct CraneCont_n_ {};

    using CraneFrame = std::variant<CraneEnter, CraneCont_n_>;
    uint64_t _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{n});
    /// Loopified apply_n_times: CraneEnter -> CraneCont_n_.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        uint64_t n = _f.n;
        if (n <= 0) {
          _result = x;
        } else {
          uint64_t n_ = n - 1;
          _stack.emplace_back(CraneCont_n_{});
          _stack.emplace_back(CraneEnter{n_});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_n_>(_frame));
        _result = f(std::move(_result));
      }
    }
    return _result;
  }

  static constexpr uint64_t test_apply_n = UINT64_C(50);
  /// TEST 12: Closure that partially applies a fixpoint.
  /// The fixpoint itself takes a function argument.
  static constexpr uint64_t test_partial_fix = UINT64_C(40);
};

#endif // INCLUDED_MEM_SAFETY_PROBE3
