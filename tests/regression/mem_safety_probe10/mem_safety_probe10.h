#ifndef INCLUDED_MEM_SAFETY_PROBE10
#define INCLUDED_MEM_SAFETY_PROBE10

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

struct MemSafetyProbe10 {
  /// Probe 10: Recursive functions that RETURN closures.
  /// Tests whether return_captures_by_value processes lambdas
  /// correctly through loopification.
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

    /// TEST 8: Closure returned from function, capturing a TREE value.
    /// The tree is a value type with unique_ptr self-references.
    /// Tests whether = capture correctly deep-copies the tree.
    uint64_t make_tree_summer(uint64_t n) const {
      return (this->tree_sum() + n);
    }

    /// TEST 5: Closure capturing value from OUTER match,
    /// returned from INNER match. Tests nested match +
    /// capture interaction.
    uint64_t nested_match_closure(bool b, uint64_t n) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return n;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        if (b) {
          return ((a0->tree_sum() + a1) + n);
        } else {
          return ((a2->tree_sum() + a1) + n);
        }
      }
    }

    /// TEST 1: Recursive function that returns a closure.
    /// Each level composes the closure from recursive results.
    /// After loopification, these closures are assigned to _result,
    /// not returned via Sreturn.
    uint64_t tree_to_adder(uint64_t x0_) const {
      const tree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const tree *_self;
        uint64_t x0_;
      };

      using CraneFrame = std::variant<CraneEnter>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self, x0_});
      /// Loopified tree_to_adder: CraneEnter.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const tree *_self = _f._self;
        uint64_t x0_ = _f.x0_;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
          _result = std::move(x0_);
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
          crane::fn<uint64_t(uint64_t)> fl = [&](uint64_t _x0) -> uint64_t {
            return a0->tree_to_adder(_x0);
          };
          crane::fn<uint64_t(uint64_t)> fr = [&](uint64_t _x0) -> uint64_t {
            return a2->tree_to_adder(_x0);
          };
          _result = fl((a1 + fr(x0_)));
        }
      }
      return _result;
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

  static uint64_t sum_fns(const mylist<crane::fn<uint64_t(uint64_t)>> &l);
  static inline const uint64_t test_tree_adder = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                        UINT64_C(20),
                        tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
    return std::move(t).tree_to_adder(UINT64_C(5));
  }();

  /// TEST 2: Build closures during list traversal,
  /// where each closure captures the HEAD of the list
  /// and the closure from the previous step.
  static uint64_t chain_adders(const mylist<uint64_t> &l,
                               const crane::fn<uint64_t(uint64_t)> &acc,
                               uint64_t x0_) {
    crane::fn<uint64_t(uint64_t)> _loop_acc = acc;
    mylist<uint64_t> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename mylist<uint64_t>::Mynil>(
              _loop_l.v())) {
        return _loop_acc(x0_);
      } else {
        const auto &[a0, a1] =
            std::get<typename mylist<uint64_t>::Mycons>(_loop_l.v());
        const mylist<uint64_t> &a1_value = *a1;
        _loop_acc = [=](uint64_t n) { return _loop_acc((a0 + n)); };
        _loop_l = a1_value;
      }
    }
  }

  static inline const uint64_t test_chain = []() {
    mylist<uint64_t> l = mylist<uint64_t>::mycons(
        UINT64_C(10),
        mylist<uint64_t>::mycons(
            UINT64_C(20),
            mylist<uint64_t>::mycons(UINT64_C(30), mylist<uint64_t>::mynil())));
    return chain_adders(
        std::move(l), [](uint64_t x) { return x; }, UINT64_C(7));
  }();
  /// TEST 3: Recursive function returning a list of closures.
  /// Each closure captures the tree node's value and subtrees.
  static mylist<crane::fn<uint64_t(uint64_t)>> collect_adders(const tree &t);
  static inline const uint64_t test_collect_adders = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(5), tree::leaf()),
                        UINT64_C(10),
                        tree::node(tree::leaf(), UINT64_C(15), tree::leaf()));
    return sum_fns(collect_adders(std::move(t)));
  }();
  /// TEST 4: Closure returned from nested match.
  /// Tests return_captures_by_value through Sif branches.
  static uint64_t choose_fn(const std::optional<bool> &o, uint64_t v,
                            uint64_t n);
  static inline const uint64_t test_choose = []() {
    crane::fn<uint64_t(uint64_t)> f1 = [](uint64_t _x0) -> uint64_t {
      return choose_fn(std::make_optional<bool>(true), UINT64_C(10), _x0);
    };
    crane::fn<uint64_t(uint64_t)> f2 = [](uint64_t _x0) -> uint64_t {
      return choose_fn(std::make_optional<bool>(false), UINT64_C(3), _x0);
    };
    crane::fn<uint64_t(uint64_t)> f3 = [](uint64_t _x0) -> uint64_t {
      return choose_fn(std::optional<bool>(), UINT64_C(99), _x0);
    };
    return ((f1(UINT64_C(5)) + f2(UINT64_C(7))) + f3(UINT64_C(42)));
  }();
  static inline const uint64_t test_nested = []() {
    return []() {
      tree t = tree::node(tree::node(tree::leaf(), UINT64_C(5), tree::leaf()),
                          UINT64_C(10),
                          tree::node(tree::leaf(), UINT64_C(15), tree::leaf()));
      crane::fn<uint64_t(uint64_t)> f1 = [=](uint64_t _x0) -> uint64_t {
        return t.nested_match_closure(true, _x0);
      };
      crane::fn<uint64_t(uint64_t)> f2 = [&](uint64_t _x0) -> uint64_t {
        return std::move(t).nested_match_closure(false, _x0);
      };
      return (f1(UINT64_C(0)) + f2(UINT64_C(0)));
    }();
  }();
  /// TEST 6: Function returning closure in pair.
  /// Tests pair construction with closure.
  static std::pair<crane::fn<uint64_t(uint64_t)>, uint64_t>
  pair_with_fn(uint64_t n);
  static inline const uint64_t test_pair_fn = []() {
    std::pair<crane::fn<uint64_t(uint64_t)>, uint64_t> p =
        pair_with_fn(UINT64_C(10));
    return (p.first(UINT64_C(5)) + p.second);
  }();
  /// TEST 7: Mutually recursive functions using a fixpoint
  /// where one captures the other's result as a closure.
  static mylist<crane::fn<uint64_t(uint64_t)>> build_tree_fns(const tree &t,
                                                              uint64_t depth);
  static inline const uint64_t test_tree_fns = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                        UINT64_C(7),
                        tree::node(tree::leaf(), UINT64_C(11), tree::leaf()));
    return sum_fns(build_tree_fns(std::move(t), UINT64_C(2)));
  }();
  static inline const uint64_t test_tree_capture = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(100), tree::leaf()),
                        UINT64_C(200),
                        tree::node(tree::leaf(), UINT64_C(300), tree::leaf()));
    return std::move(t).make_tree_summer(UINT64_C(0));
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE10
