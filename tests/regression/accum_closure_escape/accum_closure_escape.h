#ifndef INCLUDED_ACCUM_CLOSURE_ESCAPE
#define INCLUDED_ACCUM_CLOSURE_ESCAPE

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

struct AccumClosureEscape {
  /// This test explores closure escape through ACCUMULATOR patterns,
  /// which are different from the direct-return-in-constructor pattern
  /// tested by the other wip tests.
  ///
  /// Key difference: closures are built up in an accumulator during
  /// recursion. Each recursive step adds a new closure to a list.
  /// The closures capture pattern variables from the current match
  /// scope, which may be references into shared_ptr nodes.
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

    mylist<A> mylist_append(mylist<A> l2) const {
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

  /// A simple tree for supplying values.
  struct tree {
    // TYPES
    struct TLeaf {};

    struct TNode {
      std::shared_ptr<tree> a0;
      uint64_t a1;
      std::shared_ptr<tree> a2;
    };

    using variant_t = std::variant<TLeaf, TNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(TLeaf _v) : v_(_v) {}

    explicit tree(TNode _v) : v_(std::move(_v)) {}

    static tree tleaf() { return tree(TLeaf{}); }

    static tree tnode(tree a0, uint64_t a1, tree a2) {
      return tree(TNode{std::make_shared<tree>(std::move(a0)), a1,
                        std::make_shared<tree>(std::move(a2))});
    }

    // MANIPULATORS
    ~tree() {
      crane::small_vector<std::shared_ptr<tree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<TNode>(&_v)) {
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

    /// Build closures from TREE traversal: tree nodes become closures.
    /// Each closure captures pattern variables from tree match.
    mylist<crane::fn<uint64_t(uint64_t)>> tree_to_adders() const {
      const tree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const tree *_self;
      };

      /// CraneCont_TNode: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_TNode {
        uint64_t a1;
        std::shared_ptr<tree> a2;
      };

      /// CraneCont_TNode_1: saves [_tmp2, a1], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_TNode_1 {
        mylist<crane::fn<uint64_t(uint64_t)>> _tmp2;
        uint64_t a1;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_TNode, CraneCont_TNode_1>;
      mylist<crane::fn<uint64_t(uint64_t)>> _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified tree_to_adders: CraneEnter -> CraneCont_TNode ->
      /// CraneCont_TNode_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::TLeaf>(_sv.v())) {
            _result = mylist<crane::fn<uint64_t(uint64_t)>>::mynil();
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::TNode>(_sv.v());
            const tree &a0_value = *a0;
            const tree &a2_value = *a2;
            _stack.emplace_back(CraneCont_TNode{a1, a2});
            _stack.emplace_back(CraneEnter{&a0_value});
          }
        } else if (std::holds_alternative<CraneCont_TNode>(_frame)) {
          auto _f = std::move(std::get<CraneCont_TNode>(_frame));
          uint64_t a1 = _f.a1;
          std::shared_ptr<tree> a2 = std::move(_f.a2);
          const tree &a2_value = *a2;
          _stack.emplace_back(CraneCont_TNode_1{std::move(_result), a1});
          _stack.emplace_back(CraneEnter{&a2_value});
        } else {
          auto _f = std::move(std::get<CraneCont_TNode_1>(_frame));
          uint64_t a1 = _f.a1;
          _result = mylist<crane::fn<uint64_t(uint64_t)>>::mycons(
              [=](uint64_t x) { return (a1 + x); },
              std::move(_f._tmp2).mylist_append(std::move(_result)));
        }
      }
      return _result;
    }

    mylist<uint64_t> tree_to_list() const {
      const tree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const tree *_self;
      };

      /// CraneCont_TNode: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_TNode {
        uint64_t a1;
        std::shared_ptr<tree> a2;
      };

      /// CraneCont_TNode_1: saves [_tmp2, a1], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_TNode_1 {
        mylist<uint64_t> _tmp2;
        uint64_t a1;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_TNode, CraneCont_TNode_1>;
      mylist<uint64_t> _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified tree_to_list: CraneEnter -> CraneCont_TNode ->
      /// CraneCont_TNode_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::TLeaf>(_sv.v())) {
            _result = mylist<uint64_t>::mynil();
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::TNode>(_sv.v());
            _stack.emplace_back(CraneCont_TNode{a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_TNode>(_frame)) {
          auto _f = std::move(std::get<CraneCont_TNode>(_frame));
          uint64_t a1 = _f.a1;
          std::shared_ptr<tree> a2 = std::move(_f.a2);
          _stack.emplace_back(CraneCont_TNode_1{std::move(_result), a1});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<CraneCont_TNode_1>(_frame));
          uint64_t a1 = _f.a1;
          _result = mylist<uint64_t>::mycons(
              a1, std::move(_f._tmp2).mylist_append(std::move(_result)));
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

      /// CraneCont_TNode: saves [a0, a1, a2], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_TNode {
        std::shared_ptr<tree> a0;
        uint64_t a1;
        std::shared_ptr<tree> a2;
      };

      /// CraneCont_TNode_1: saves [_tmp2, a0, a1, a2], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_TNode_1 {
        T1 _tmp2;
        std::shared_ptr<tree> a0;
        uint64_t a1;
        std::shared_ptr<tree> a2;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_TNode, CraneCont_TNode_1>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified tree_rect: CraneEnter -> CraneCont_TNode ->
      /// CraneCont_TNode_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::TLeaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::TNode>(_sv.v());
            _stack.emplace_back(CraneCont_TNode{a0, a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_TNode>(_frame)) {
          auto _f = std::move(std::get<CraneCont_TNode>(_frame));
          std::shared_ptr<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          std::shared_ptr<tree> a2 = std::move(_f.a2);
          _stack.emplace_back(
              CraneCont_TNode_1{std::move(_result), std::move(a0), a1, a2});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<CraneCont_TNode_1>(_frame));
          std::shared_ptr<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          std::shared_ptr<tree> a2 = std::move(_f.a2);
          _result = f0(*a0, std::move(_f._tmp2), a1, *a2, std::move(_result));
        }
      }
      return _result;
    }
  };

  /// Fold-left that builds a closure from each element.
  ///
  /// SIMPLE LAMBDA VERSION: Each closure fun x => h + x captures
  /// h from the pattern match. These are simple lambdas, so they
  /// should capture by =.
  static mylist<crane::fn<uint64_t(uint64_t)>>
  build_adders(const mylist<uint64_t> &l,
               mylist<crane::fn<uint64_t(uint64_t)>> acc);
  /// Apply first closure from the list.
  static uint64_t apply_first(const mylist<crane::fn<uint64_t(uint64_t)>> &fns,
                              uint64_t x);
  /// Apply all closures and sum.
  static uint64_t
  apply_all_sum(const mylist<crane::fn<uint64_t(uint64_t)>> &fns, uint64_t x);
  /// test1: build_adders 10, 20, 30  = 30+_, 20+_, 10+_ (reversed)
  /// apply_first result 5 = 30 + 5 = 35
  static inline const uint64_t test1 = []() {
    mylist<crane::fn<uint64_t(uint64_t)>> fns = build_adders(
        mylist<uint64_t>::mycons(
            UINT64_C(10),
            mylist<uint64_t>::mycons(
                UINT64_C(20), mylist<uint64_t>::mycons(
                                  UINT64_C(30), mylist<uint64_t>::mynil()))),
        mylist<crane::fn<uint64_t(uint64_t)>>::mynil());
    return apply_first(std::move(fns), UINT64_C(5));
  }();
  /// test2: apply all closures: (30+5) + (20+5) + (10+5) = 35+25+15 = 75
  static inline const uint64_t test2 = []() {
    mylist<crane::fn<uint64_t(uint64_t)>> fns = build_adders(
        mylist<uint64_t>::mycons(
            UINT64_C(10),
            mylist<uint64_t>::mycons(
                UINT64_C(20), mylist<uint64_t>::mycons(
                                  UINT64_C(30), mylist<uint64_t>::mynil()))),
        mylist<crane::fn<uint64_t(uint64_t)>>::mynil());
    return apply_all_sum(std::move(fns), UINT64_C(5));
  }();

  /// COMPOSE CLOSURES: Each step builds a composed function.
  /// This creates closures that capture OTHER closures.
  static uint64_t compose_from_list(const mylist<uint64_t> &l,
                                    crane::fn<uint64_t(uint64_t)> acc,
                                    uint64_t x0_) {
    if (std::holds_alternative<typename mylist<uint64_t>::Mynil>(l.v())) {
      return acc(x0_);
    } else {
      const auto &[a0, a1] = std::get<typename mylist<uint64_t>::Mycons>(l.v());
      const mylist<uint64_t> &a1_value = *a1;
      return compose_from_list(
          a1_value, [=](uint64_t x) { return acc((a0 + x)); }, x0_);
    }
  }

  /// test3: compose_from_list 10, 20, 30 id
  /// = fun x => id (10 + (20 + (30 + x)))
  /// = fun x => 60 + x
  /// test3 = 60 + 7 = 67
  static inline const uint64_t test3 = compose_from_list(
      mylist<uint64_t>::mycons(
          UINT64_C(10),
          mylist<uint64_t>::mycons(
              UINT64_C(20), mylist<uint64_t>::mycons(
                                UINT64_C(30), mylist<uint64_t>::mynil()))),
      [](uint64_t x) { return x; }, UINT64_C(7));
  /// test4: Tree (Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf))
  /// Closures: 20+_, 10+_, 30+_
  /// apply_all_sum with 5: (20+5) + (10+5) + (30+5) = 25+15+35 = 75
  static inline const uint64_t test4 = []() {
    tree t = tree::tnode(
        tree::tnode(tree::tleaf(), UINT64_C(10), tree::tleaf()), UINT64_C(20),
        tree::tnode(tree::tleaf(), UINT64_C(30), tree::tleaf()));
    return apply_all_sum(std::move(t).tree_to_adders(), UINT64_C(5));
  }();
  /// Store a closure and then clobber the stack before using it.
  static inline const uint64_t test5 = []() {
    tree t =
        tree::tnode(tree::tnode(tree::tleaf(), UINT64_C(42), tree::tleaf()),
                    UINT64_C(100), tree::tleaf());
    mylist<crane::fn<uint64_t(uint64_t)>> fns = std::move(t).tree_to_adders();
    return apply_first(std::move(fns), UINT64_C(0));
  }();
};

#endif // INCLUDED_ACCUM_CLOSURE_ESCAPE
