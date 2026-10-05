#ifndef INCLUDED_MEM_SAFETY_PROBE24
#define INCLUDED_MEM_SAFETY_PROBE24

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

struct MemSafetyProbe24 {
  /// Probe 24: Complex value-type interactions.
  ///
  /// Attack vectors:
  /// 1. Use-after-move in pair/constructor arguments: if Crane
  /// generates std::move(t) alongside t.field in the same expression
  /// 2. Rose-tree with list children: complex ownership when
  /// flattening nested value types
  /// 3. Multi-use of owned variable in constructor calls: t used in
  /// both constructor position AND field-access position
  /// 4. Value-type stored in option/pair then accessed through
  /// projection — tests whether projections access moved-from data
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

    /// TEST 6: Store a tree AND its sum in a pair, then transform
    /// both. Tests that clone is independent of original.
    uint64_t clone_and_transform() const {
      std::pair<tree, uint64_t> p = std::make_pair(*this, this->tree_sum());
      tree t2 = p.first;
      uint64_t s = std::move(p).second;
      tree t3 = std::move(t2).map_tree([=](uint64_t n) { return (n + s); });
      return std::move(t3).tree_sum();
    }

    /// TEST 5: Nested value type — list of trees stored in a tree-like
    /// structure. Tests clone correctness and ownership for nested types.
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

    /// TEST 4: Recursive function where result uses BOTH t (for return)
    /// and t's children (through recursive calls) — not loopified because
    /// return type is pair. Tests use-after-move in make_pair.
    std::pair<tree, uint64_t> tag_tree() const {
      const tree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const tree *_self;
      };

      /// CraneCont_Node: saves [_self, a1, a2], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Node {
        const tree *_self;
        uint64_t a1;
        std::shared_ptr<tree> a2;
      };

      /// CraneCont_Node_1: saves [_self, a1, pl], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Node_1 {
        const tree *_self;
        uint64_t a1;
        std::pair<tree, uint64_t> pl;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
      std::pair<tree, uint64_t> _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified tag_tree: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = std::make_pair(tree::leaf(), UINT64_C(0));
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(CraneCont_Node{_self, a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Node>(_frame));
          const tree *_self = _f._self;
          uint64_t a1 = _f.a1;
          std::shared_ptr<tree> a2 = std::move(_f.a2);
          std::pair<tree, uint64_t> pl = std::move(_result);
          _stack.emplace_back(CraneCont_Node_1{_self, a1, std::move(pl)});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
          const tree *_self = _f._self;
          uint64_t a1 = _f.a1;
          std::pair<tree, uint64_t> pl = std::move(_f.pl);
          std::pair<tree, uint64_t> pr = std::move(_result);
          _result = std::make_pair(
              *_self, ((a1 + std::move(pl).second) + std::move(pr).second));
        }
      }
      return _result;
    }

    /// TEST 3: Triple use of t in one expression.
    std::pair<std::pair<tree, tree>, uint64_t> triple_use() const {
      return std::make_pair(std::make_pair(*this, *this), this->tree_sum());
    }

    /// TEST 2: Pair where BOTH elements use t, one as value
    /// and one through a function.
    std::pair<tree, uint64_t> pair_self() const {
      return std::make_pair(*this, this->tree_sum());
    }

    /// TEST 1: Variable used as BOTH whole value AND for field access
    /// in the same constructor. In C++, tree::node(t, tree_sum(t), Leaf)
    /// where t must be cloned and tree_sum accesses t's children.
    tree self_annotate() const {
      return tree::node(*this, this->tree_sum(), tree::leaf());
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
      return this->template tree_rect<T1>(std::move(f), f0);
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

    uint64_t length() const {
      const mylist<A> *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const mylist<A> *_self;
      };

      /// CraneCont_Mycons: resumes after recursive call, then processes rest.
      struct CraneCont_Mycons {};

      using CraneFrame = std::variant<CraneEnter, CraneCont_Mycons>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified length: CraneEnter -> CraneCont_Mycons.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const mylist<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename mylist<A>::Mynil>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1] =
                std::get<typename mylist<A>::Mycons>(_sv.v());
            _stack.emplace_back(CraneCont_Mycons{});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<CraneCont_Mycons>(_frame));
          _result = (UINT64_C(1) + std::move(_result));
        }
      }
      return _result;
    }

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

    template <typename T1, typename F1> T1 mylist_rec(T1 f, F1 &&f0) const {
      return this->template mylist_rect<T1>(std::move(f), f0);
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
  static inline const uint64_t test_self_annotate =
      tree::node(tree::leaf(), UINT64_C(5), tree::leaf())
          .self_annotate()
          .tree_sum();
  static inline const uint64_t test_pair_self = []() {
    std::pair<tree, uint64_t> p =
        tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                   UINT64_C(7),
                   tree::node(tree::leaf(), UINT64_C(11), tree::leaf()))
            .pair_self();
    return (p.first.tree_sum() + p.second);
  }();
  static inline const uint64_t test_triple_use = []() {
    std::pair<std::pair<tree, tree>, uint64_t> p =
        tree::node(tree::leaf(), UINT64_C(5), tree::leaf()).triple_use();
    return (((p.first).first.tree_sum() + (p.first).second.tree_sum()) +
            p.second);
  }();
  static inline const uint64_t test_tag_tree = []() {
    std::pair<tree, uint64_t> p =
        tree::node(tree::node(tree::leaf(), UINT64_C(2), tree::leaf()),
                   UINT64_C(5),
                   tree::node(tree::leaf(), UINT64_C(8), tree::leaf()))
            .tag_tree();
    return (p.first.tree_sum() + p.second);
  }();
  static mylist<uint64_t> tree_to_list(const tree &t);
  static inline const uint64_t test_nested_ops = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                        UINT64_C(7),
                        tree::node(tree::leaf(), UINT64_C(11), tree::leaf()));
    tree doubled = t.map_tree([](uint64_t n) { return (n * UINT64_C(2)); });
    mylist<uint64_t> flat = tree_to_list(std::move(doubled));
    return (sum_list(std::move(flat)) + std::move(t).tree_sum());
  }();
  static inline const uint64_t test_clone_and_transform =
      tree::node(tree::node(tree::leaf(), UINT64_C(1), tree::leaf()),
                 UINT64_C(2),
                 tree::node(tree::leaf(), UINT64_C(3), tree::leaf()))
          .clone_and_transform();
  /// TEST 7: Build a tree from a list, using accumulated state.
  /// Tests interaction between list recursion and tree construction.
  static tree list_to_tree(const mylist<uint64_t> &l, tree acc);
  static inline const uint64_t test_list_to_tree =
      list_to_tree(
          mylist<uint64_t>::mycons(
              UINT64_C(1),
              mylist<uint64_t>::mycons(
                  UINT64_C(2), mylist<uint64_t>::mycons(
                                   UINT64_C(3), mylist<uint64_t>::mynil()))),
          tree::leaf())
          .tree_sum();
  /// TEST 8: Zip two trees, producing a list of pairs.
  /// Both trees are destructured simultaneously.
  static mylist<std::pair<uint64_t, uint64_t>> zip_trees(const tree &t1,
                                                         const tree &t2);

  static inline const uint64_t test_zip_trees = sum_list([]() {
    mylist<std::pair<uint64_t, uint64_t>> pairs = zip_trees(
        tree::node(tree::node(tree::leaf(), UINT64_C(1), tree::leaf()),
                   UINT64_C(2),
                   tree::node(tree::leaf(), UINT64_C(3), tree::leaf())),
        tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                   UINT64_C(20),
                   tree::node(tree::leaf(), UINT64_C(30), tree::leaf())));
    crane::fn<uint64_t(std::pair<uint64_t, uint64_t>)> add_pair =
        [](const std::pair<uint64_t, uint64_t> &p) {
          return (p.first + p.second);
        };
    if (std::holds_alternative<
            typename mylist<std::pair<uint64_t, uint64_t>>::Mynil>(
            pairs.v_mut())) {
      return mylist<uint64_t>::mycons(UINT64_C(0), mylist<uint64_t>::mynil());
    } else {
      auto &[a0, a1] =
          std::get<typename mylist<std::pair<uint64_t, uint64_t>>::Mycons>(
              pairs.v_mut());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<
              typename mylist<std::pair<uint64_t, uint64_t>>::Mynil>(
              _sv0.v())) {
        return mylist<uint64_t>::mycons(add_pair(std::move(a0)),
                                        mylist<uint64_t>::mynil());
      } else {
        const auto &[a00, a10] =
            std::get<typename mylist<std::pair<uint64_t, uint64_t>>::Mycons>(
                _sv0.v());
        auto &&_sv1 = *a10;
        if (std::holds_alternative<
                typename mylist<std::pair<uint64_t, uint64_t>>::Mynil>(
                _sv1.v())) {
          return mylist<uint64_t>::mycons(
              add_pair(std::move(a0)),
              mylist<uint64_t>::mycons(add_pair(a00),
                                       mylist<uint64_t>::mynil()));
        } else {
          const auto &[a01, a11] =
              std::get<typename mylist<std::pair<uint64_t, uint64_t>>::Mycons>(
                  _sv1.v());
          return mylist<uint64_t>::mycons(
              add_pair(std::move(a0)),
              mylist<uint64_t>::mycons(
                  add_pair(a00),
                  mylist<uint64_t>::mycons(add_pair(a01),
                                           mylist<uint64_t>::mynil())));
        }
      }
    }
  }());
};

#endif // INCLUDED_MEM_SAFETY_PROBE24
