#ifndef INCLUDED_MEM_SAFETY_PROBE2
#define INCLUDED_MEM_SAFETY_PROBE2

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

struct MemSafetyProbe2 {
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

    /// TEST 18: Construct a tree using partial app results, then traverse it.
    tree build_from_partial() const {
      uint64_t v = this->sum_values(UINT64_C(0));
      return tree::node(tree::node(tree::leaf(), v, tree::leaf()), v,
                        tree::node(tree::leaf(), v, tree::leaf()));
    }

    /// TEST 16: Closure captured in a match branch that also destructs a tree.
    /// The closure captures a value-type match-bound field.
    uint64_t capture_in_branch(const tree &) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        crane::fn<uint64_t(uint64_t)> f = [&](uint64_t _x0) -> uint64_t {
          return a0->sum_values(_x0);
        };
        return (f(a1) + a2->sum_values(a1));
      }
    }

    /// TEST 15: Multiple closures applied in sequence, each consuming a tree.
    uint64_t apply_chain(tree t2, const tree &t3, uint64_t x) const {
      crane::fn<uint64_t(uint64_t)> f1 = [&](uint64_t _x0) -> uint64_t {
        return std::move(*this).sum_values(_x0);
      };
      crane::fn<uint64_t(uint64_t)> f2 = [&](uint64_t _x0) -> uint64_t {
        return std::move(t2).sum_values(_x0);
      };
      return t3.sum_values(f2(f1(x)));
    }

    /// TEST 14: Partial application stored in pair alongside tree.
    std::pair<crane::fn<uint64_t(uint64_t)>, tree> pair_closure_tree() const {
      tree _self_val = *this;
      return std::make_pair(
          [=](uint64_t _x0) -> uint64_t { return _self_val.sum_values(_x0); },
          *this);
    }

    /// TEST 12: Value type cloned into pair, then both halves used with
    /// closures.
    uint64_t clone_and_close() const {
      std::pair<tree, tree> p = std::make_pair(*this, *this);
      crane::fn<uint64_t(uint64_t)> f = [=](uint64_t _x0) -> uint64_t {
        return p.first.sum_values(_x0);
      };
      crane::fn<uint64_t(uint64_t)> g = [&](uint64_t _x0) -> uint64_t {
        return std::move(p).second.sum_values(_x0);
      };
      return (f(UINT64_C(1)) + g(UINT64_C(2)));
    }

    /// TEST 11: Partial application used in BOTH branches of a match
    /// (only one branch executes).
    uint64_t branch_use(bool b) const {
      crane::fn<uint64_t(uint64_t)> f = [&](uint64_t _x0) -> uint64_t {
        return std::move(*this).sum_values(_x0);
      };
      if (b) {
        return f(UINT64_C(0));
      } else {
        return f(UINT64_C(100));
      }
    }

    /// TEST 9: Option wrapping a closure.
    std::optional<crane::fn<uint64_t(uint64_t)>> opt_adder(bool b) const {
      tree _self_val = *this;
      if (b) {
        return std::make_optional<crane::fn<uint64_t(uint64_t)>>(
            [=](uint64_t _x0) -> uint64_t {
              return std::move(_self_val).sum_values(_x0);
            });
      } else {
        return std::optional<crane::fn<uint64_t(uint64_t)>>();
      }
    }

    /// TEST 8: Match inside let-in where the partial application captures
    /// a match-bound field AND the match is inside a let continuation.
    /// Probes interaction between escape analysis and nested match.
    uint64_t extract_and_apply() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        crane::fn<uint64_t(uint64_t)> fl = [&](uint64_t _x0) -> uint64_t {
          return a0->sum_values(_x0);
        };
        crane::fn<uint64_t(uint64_t)> fr = [&](uint64_t _x0) -> uint64_t {
          return a2->sum_values(_x0);
        };
        return (fl(a1) + fr(a1));
      }
    }

    /// TEST 6: Value type used twice in pair.
    std::pair<tree, tree> tree_pair() const {
      return std::make_pair(*this, *this);
    }

    /// TEST 5: Closure capturing a closure.
    /// The inner closure captures a tree, the outer captures the inner closure.
    uint64_t double_wrap(uint64_t x) const {
      crane::fn<uint64_t(uint64_t)> f = [&](uint64_t _x0) -> uint64_t {
        return std::move(*this).sum_values(_x0);
      };
      return (f(x) + x);
    }

    /// TEST 4: Partial application of a wrapper that stores its arg in a
    /// constructor.
    tree make_node(uint64_t v, const tree &r) const {
      return tree::node(*this, v, r);
    }

    /// TEST 3: Compose two closures, each capturing a different tree.
    uint64_t compose_adders(const tree &t2, uint64_t x) const {
      return this->sum_values(t2.sum_values(x));
    }

    /// TEST 2: CPS-style: pass a continuation that captures value types.
    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, crane::fn<uint64_t(uint64_t)>>
    T1 with_tree(F0 &&k) const {
      tree _self_val = *this;
      return k(
          [=](uint64_t _x0) -> uint64_t { return _self_val.sum_values(_x0); });
    }

    /// TEST 1: Use value type in both a partial application AND as a
    /// constructor arg. Tests whether the move analysis correctly handles
    /// double-use.
    std::pair<tree, uint64_t> dup_tree() const {
      return std::make_pair(tree::node(*this, UINT64_C(0), tree::leaf()),
                            this->sum_values(UINT64_C(0)));
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

    mylist<A> myrev() const { return this->myrev_append(mylist<A>::mynil()); }

    /// TEST 17: Build a list of closures, reverse it, and apply all.
    /// Probes whether closures survive list operations.
    mylist<A> myrev_append(mylist<A> acc) const {
      const mylist<A> *_loop_self = this;
      mylist<A> _loop_acc = std::move(acc);
      while (true) {
        auto &&_sv = *_loop_self;
        if (std::holds_alternative<typename mylist<A>::Mynil>(_sv.v())) {
          return _loop_acc;
        } else {
          const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(_sv.v());
          _loop_self = crane_raw(a1);
          _loop_acc = mylist<A>::mycons(a0, std::move(_loop_acc));
        }
      }
    }

    uint64_t mylength() const {
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

    template <typename T1, typename F1> T1 mylist_rec(T1 f, F1 &&f0) const {
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
      /// Loopified mylist_rec: CraneEnter -> CraneCont_Mycons.
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

  static inline const uint64_t test_dup_tree = []() {
    tree t = tree::node(tree::leaf(), UINT64_C(42), tree::leaf());
    std::pair<tree, uint64_t> p = std::move(t).dup_tree();
    return (p.first.sum_values(UINT64_C(0)) + p.second);
  }();
  static constexpr uint64_t test_cps = UINT64_C(125);
  static constexpr uint64_t test_compose = UINT64_C(35);
  static constexpr uint64_t test_partial_ctor = UINT64_C(42);
  static constexpr uint64_t test_double_wrap = UINT64_C(62);
  static inline const uint64_t test_tree_pair = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                        UINT64_C(20),
                        tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
    std::pair<tree, tree> p = std::move(t).tree_pair();
    return (p.first.sum_values(UINT64_C(0)) + p.second.sum_values(UINT64_C(0)));
  }();
  /// TEST 7: Closure escaping through a list, then applied.
  static mylist<uint64_t>
  map_apply(const mylist<crane::fn<uint64_t(uint64_t)>> &fs, uint64_t x);
  static uint64_t mysum(const mylist<uint64_t> &l);
  static constexpr uint64_t test_closure_escape_list = UINT64_C(40);
  static constexpr uint64_t test_extract_apply = UINT64_C(80);
  static constexpr uint64_t test_opt_closure = UINT64_C(52);
  /// TEST 10: Two partial applications of the SAME function
  /// with DIFFERENT captured values. Both must independently own data.
  static constexpr uint64_t test_two_partial = UINT64_C(30);
  static constexpr uint64_t test_branch_true = UINT64_C(60);
  /// f 0 = 60
  static constexpr uint64_t test_branch_false = UINT64_C(160);
  /// With t = Node Leaf 42 Leaf: 43 + 44 = 87
  static inline const uint64_t test_clone_close =
      tree::node(tree::leaf(), UINT64_C(42), tree::leaf()).clone_and_close();
  /// TEST 13: Fold building tree from closures' results.
  static tree fold_tree_build(const mylist<crane::fn<uint64_t(uint64_t)>> &fs,
                              uint64_t acc);
  static constexpr uint64_t test_fold_tree = UINT64_C(35);
  static inline const uint64_t test_pair_closure_tree = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                        UINT64_C(20),
                        tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
    std::pair<crane::fn<uint64_t(uint64_t)>, tree> p =
        std::move(t).pair_closure_tree();
    return (p.first(UINT64_C(5)) + p.second.sum_values(UINT64_C(0)));
  }();
  static constexpr uint64_t test_chain = UINT64_C(65);
  static constexpr uint64_t test_capture_branch = UINT64_C(80);
  static uint64_t apply_all(const mylist<crane::fn<uint64_t(uint64_t)>> &fs,
                            uint64_t x);
  static constexpr uint64_t test_rev_closures = UINT64_C(75);
  static constexpr uint64_t test_build_from_partial = UINT64_C(180);
};

#endif // INCLUDED_MEM_SAFETY_PROBE2
