#ifndef INCLUDED_MEM_SAFETY_PROBE6
#define INCLUDED_MEM_SAFETY_PROBE6

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

struct MemSafetyProbe6 {
  /// These tests probe closures that capture RECURSIVE self-reference
  /// fields from match bindings. In C++, these fields are unique_ptr.
  /// A lambda capturing a unique_ptr by = fails (non-copyable).
  /// A lambda capturing by & would dangle if returned.
  /// Crane must pre-copy or clone the field.
  ///
  /// NOTE: All functions use nat as FIRST argument to avoid
  /// methodification bugs with curried return types.
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

    /// TEST 3: Closure returned from match that applies a function
    /// to the tail — forces unique_ptr access and HOF.
    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, const A &>
    mylist<T1> mymap(F0 &&f) const {
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

    /// TEST 2: Closure from match that reconstructs using both
    /// a value field and a recursive field.
    mylist<A> head_and_tail(uint64_t, const A &, const A &) const {
      if (std::holds_alternative<typename mylist<A>::Mynil>(this->v())) {
        return mylist<A>::mynil();
      } else {
        const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(this->v());
        return mylist<A>::mycons(a0, *a1);
      }
    }

    /// TEST 1: Return a closure that uses the TAIL of the list.
    /// xs is a unique_ptr<mylist> field — the closure must clone it.
    uint64_t tail_adder(uint64_t, uint64_t n) const {
      if (std::holds_alternative<typename mylist<A>::Mynil>(this->v())) {
        return n;
      } else {
        const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(this->v());
        return (a1->length() + n);
      }
    }

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

  static inline const uint64_t test_tail_adder = []() {
    mylist<uint64_t> l = mylist<uint64_t>::mycons(
        UINT64_C(1),
        mylist<uint64_t>::mycons(
            UINT64_C(2),
            mylist<uint64_t>::mycons(UINT64_C(3), mylist<uint64_t>::mynil())));
    return std::move(l).tail_adder(UINT64_C(0), UINT64_C(100));
  }();
  static inline const uint64_t test_head_and_tail = []() {
    return []() {
      mylist<uint64_t> l = mylist<uint64_t>::mycons(
          UINT64_C(10),
          mylist<uint64_t>::mycons(UINT64_C(20), mylist<uint64_t>::mynil()));
      crane::fn<mylist<uint64_t>(uint64_t)> f =
          [&](uint64_t _x0) -> mylist<uint64_t> {
        return std::move(l).head_and_tail(UINT64_C(0), UINT64_C(0), _x0);
      };
      mylist<uint64_t> l2 = f(UINT64_C(99));
      return std::move(l2).length();
    }();
  }();

  /// f reconstructs the list 10, 20. length 10,20 = 2
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
      if (std::holds_alternative<Leaf>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<Node>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a2 && _alt->a2.use_count() == 1))) {
          return;
        }
      }
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

    /// TEST 4: Return a closure that captures BOTH subtrees of a tree.
    /// Both l and r are unique_ptr fields.
    tree both_subtrees(uint64_t, bool x) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return tree::leaf();
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        if (x) {
          return *a0;
        } else {
          return *a2;
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

  template <typename F2>
  static mylist<uint64_t> tail_mapper(uint64_t, const mylist<uint64_t> &l,
                                      F2 &&x) {
    if (std::holds_alternative<typename mylist<uint64_t>::Mynil>(l.v())) {
      return mylist<uint64_t>::mynil();
    } else {
      const auto &[a0, a1] = std::get<typename mylist<uint64_t>::Mycons>(l.v());
      return mylist<uint64_t>::mycons(a0, a1->template mymap<uint64_t>(x));
    }
  }

  static inline const uint64_t test_tail_mapper = []() {
    return []() {
      mylist<uint64_t> l = mylist<uint64_t>::mycons(
          UINT64_C(1),
          mylist<uint64_t>::mycons(
              UINT64_C(2), mylist<uint64_t>::mycons(
                               UINT64_C(3), mylist<uint64_t>::mynil())));
      crane::fn<mylist<uint64_t>(crane::fn<uint64_t(uint64_t)>)> f =
          [&](crane::fn<uint64_t(uint64_t)> _x0) -> mylist<uint64_t> {
        return tail_mapper(UINT64_C(0), std::move(l), _x0);
      };
      mylist<uint64_t> l2 = f([](uint64_t n) { return (n * UINT64_C(10)); });
      return std::move(l2).length();
    }();
  }();
  static inline const uint64_t test_both_subtrees = []() {
    return []() {
      tree t = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                          UINT64_C(20),
                          tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
      crane::fn<tree(bool)> sel = [=](bool _x0) -> tree {
        return std::move(t).both_subtrees(UINT64_C(0), _x0);
      };
      return (sel(true).tree_sum() + sel(false).tree_sum());
    }();
  }();
  /// TEST 5: Chain of closures each pre-computing from the tail.
  static mylist<crane::fn<uint64_t(uint64_t)>>
  build_chain(const mylist<uint64_t> &l);
  static uint64_t apply_chain(const mylist<crane::fn<uint64_t(uint64_t)>> &fns,
                              uint64_t x);
  static inline const uint64_t test_chain = []() {
    mylist<uint64_t> l = mylist<uint64_t>::mycons(
        UINT64_C(10),
        mylist<uint64_t>::mycons(
            UINT64_C(20),
            mylist<uint64_t>::mycons(UINT64_C(30), mylist<uint64_t>::mynil())));
    mylist<crane::fn<uint64_t(uint64_t)>> fns = build_chain(std::move(l));
    return apply_chain(std::move(fns), UINT64_C(0));
  }();
  /// TEST 6: Closure captures tail, then tail is used again
  /// after the closure is created — tests double use.
  static uint64_t capture_and_reuse(uint64_t _x, const mylist<uint64_t> &l);
  static inline const uint64_t test_capture_reuse = capture_and_reuse(
      UINT64_C(0),
      mylist<uint64_t>::mycons(
          UINT64_C(5),
          mylist<uint64_t>::mycons(
              UINT64_C(1), mylist<uint64_t>::mycons(
                               UINT64_C(2), mylist<uint64_t>::mynil()))));
};

#endif // INCLUDED_MEM_SAFETY_PROBE6
