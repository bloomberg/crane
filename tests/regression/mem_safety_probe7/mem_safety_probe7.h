#ifndef INCLUDED_MEM_SAFETY_PROBE7
#define INCLUDED_MEM_SAFETY_PROBE7

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct MemSafetyProbe7 {
  /// These tests FORCE closures that capture recursive self-reference
  /// fields (unique_ptr) by storing them in data structures.
  /// Closures return SCALAR values but COMPUTE from captured
  /// recursive structures (lists/trees).
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

    template <typename _U>
    mylist(const mylist<_U> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename mylist<_U>::Mynil>(
                    _other.v())) {
              return Mynil{};
            } else {
              const auto &[a0, a1] =
                  std::get<typename mylist<_U>::Mycons>(_other.v());
              return Mycons{[&]() -> A {
                              if constexpr (crane_convertible<A, const _U &>) {
                                return crane_convert<A>(a0);
                              } else {
                                throw std::logic_error(
                                    "unreachable: inactive constructor field "
                                    "at this instantiation");
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
    mylist(mylist &&) noexcept = default;
    mylist &operator=(mylist &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t length() const {
      const mylist<A> *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const mylist<A> *_self;
      };

      /// _Cont_Mycons: resumes after recursive call, then processes rest.
      struct _Cont_Mycons {};

      using _Frame = std::variant<_Enter, _Cont_Mycons>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified length: _Enter -> _Cont_Mycons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const mylist<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename mylist<A>::Mynil>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1] =
                std::get<typename mylist<A>::Mycons>(_sv.v());
            _stack.emplace_back(_Cont_Mycons{});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_Cont_Mycons>(_frame));
          _result = (UINT64_C(1) + std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, mylist<A> &, T1 &>
    T1 mylist_rec(T1 f, F1 &&f0) const {
      const mylist<A> *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const mylist<A> *_self;
      };

      /// _Cont_Mycons: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Mycons {
        A a0;
        std::shared_ptr<mylist<A>> a1;
      };

      using _Frame = std::variant<_Enter, _Cont_Mycons>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified mylist_rec: _Enter -> _Cont_Mycons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const mylist<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename mylist<A>::Mynil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] =
                std::get<typename mylist<A>::Mycons>(_sv.v());
            _stack.emplace_back(_Cont_Mycons{a0, a1});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_Cont_Mycons>(_frame));
          auto a0 = std::move(_f.a0);
          std::shared_ptr<mylist<A>> a1 = std::move(_f.a1);
          _result = f0(a0, *a1, std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, mylist<A> &, T1 &>
    T1 mylist_rect(T1 f, F1 &&f0) const {
      const mylist<A> *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const mylist<A> *_self;
      };

      /// _Cont_Mycons: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Mycons {
        A a0;
        std::shared_ptr<mylist<A>> a1;
      };

      using _Frame = std::variant<_Enter, _Cont_Mycons>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified mylist_rect: _Enter -> _Cont_Mycons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const mylist<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename mylist<A>::Mynil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] =
                std::get<typename mylist<A>::Mycons>(_sv.v());
            _stack.emplace_back(_Cont_Mycons{a0, a1});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_Cont_Mycons>(_frame));
          auto a0 = std::move(_f.a0);
          std::shared_ptr<mylist<A>> a1 = std::move(_f.a1);
          _result = f0(a0, *a1, std::move(_result));
        }
      }
      return _result;
    }
  };

  static uint64_t sum_list(const mylist<uint64_t> &l);
  /// TEST 1: Build a list of closures where each captures the TAIL
  /// and computes its length. The tail is unique_ptr.
  static mylist<crane::fn<uint64_t(std::monostate)>>
  build_len_closures(const mylist<uint64_t> &l);
  static uint64_t sum_fns(const mylist<crane::fn<uint64_t(std::monostate)>> &l);
  static inline const uint64_t test_len_closures = []() {
    mylist<uint64_t> l = mylist<uint64_t>::mycons(
        UINT64_C(1),
        mylist<uint64_t>::mycons(
            UINT64_C(2),
            mylist<uint64_t>::mycons(
                UINT64_C(3), mylist<uint64_t>::mycons(
                                 UINT64_C(4), mylist<uint64_t>::mynil()))));
    mylist<crane::fn<uint64_t(std::monostate)>> fns =
        build_len_closures(std::move(l));
    return sum_fns(std::move(fns));
  }();
  /// TEST 2: Build closures that compute the SUM of the tail.
  /// Each closure captures the entire tail sublist.
  static mylist<crane::fn<uint64_t(std::monostate)>>
  build_sum_closures(const mylist<uint64_t> &l);
  static inline const uint64_t test_sum_closures = []() {
    mylist<uint64_t> l = mylist<uint64_t>::mycons(
        UINT64_C(10),
        mylist<uint64_t>::mycons(
            UINT64_C(20),
            mylist<uint64_t>::mycons(UINT64_C(30), mylist<uint64_t>::mynil())));
    mylist<crane::fn<uint64_t(std::monostate)>> fns =
        build_sum_closures(std::move(l));
    return sum_fns(std::move(fns));
  }();

  /// Sums: sum20,30=50, sum30=30, sum=0. Total = 80.
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
    tree(tree &&) noexcept = default;
    tree &operator=(tree &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// TEST 5: Create closures that capture BOTH children of a tree
    /// and use them independently. Both l and r are unique_ptr.
    std::pair<crane::fn<uint64_t(std::monostate)>,
              crane::fn<uint64_t(std::monostate)>>
    make_subtree_getters() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return std::make_pair([](std::monostate) { return UINT64_C(0); },
                              [](std::monostate) { return UINT64_C(0); });
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        const tree &a0_value = *a0;
        const tree &a2_value = *a2;
        return std::make_pair(
            [=](std::monostate) { return a0_value.tree_sum(); },
            [=](std::monostate) { return a2_value.tree_sum(); });
      }
    }

    /// TEST 3: Build closures from tree that each capture a subtree
    /// and compute its sum.
    mylist<crane::fn<uint64_t(std::monostate)>> tree_sum_closures() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return mylist<crane::fn<uint64_t(std::monostate)>>::mynil();
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        const tree &a0_value = *a0;
        const tree &a2_value = *a2;
        return mylist<crane::fn<uint64_t(std::monostate)>>::mycons(
            [=](std::monostate) { return a0_value.tree_sum(); },
            mylist<crane::fn<uint64_t(std::monostate)>>::mycons(
                [=](std::monostate) { return a2_value.tree_sum(); },
                mylist<crane::fn<uint64_t(std::monostate)>>::mynil()));
      }
    }

    uint64_t tree_sum() const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _Cont_Node: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Node {
        uint64_t a1;
        std::shared_ptr<tree> a2;
      };

      /// _Cont_Node_1: saves [_tmp2, a1], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Node_1 {
        uint64_t _tmp2;
        uint64_t a1;
      };

      using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified tree_sum: _Enter -> _Cont_Node -> _Cont_Node_1.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_Cont_Node{a1, a2});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_Cont_Node>(_frame)) {
          auto _f = std::move(std::get<_Cont_Node>(_frame));
          uint64_t a1 = _f.a1;
          std::shared_ptr<tree> a2 = std::move(_f.a2);
          _stack.emplace_back(_Cont_Node_1{std::move(_result), a1});
          _stack.emplace_back(_Enter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<_Cont_Node_1>(_frame));
          uint64_t a1 = _f.a1;
          _result = ((_f._tmp2 + a1) + std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, uint64_t &, tree &,
                                     T1 &>
    T1 tree_rec(T1 f, F1 &&f0) const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _Cont_Node: saves [a0, a1, a2], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Node {
        std::shared_ptr<tree> a0;
        uint64_t a1;
        std::shared_ptr<tree> a2;
      };

      /// _Cont_Node_1: saves [_tmp2, a0, a1, a2], resumes after recursive call,
      /// then processes rest.
      struct _Cont_Node_1 {
        T1 _tmp2;
        std::shared_ptr<tree> a0;
        uint64_t a1;
        std::shared_ptr<tree> a2;
      };

      using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified tree_rec: _Enter -> _Cont_Node -> _Cont_Node_1.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_Cont_Node{a0, a1, a2});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_Cont_Node>(_frame)) {
          auto _f = std::move(std::get<_Cont_Node>(_frame));
          std::shared_ptr<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          std::shared_ptr<tree> a2 = std::move(_f.a2);
          _stack.emplace_back(
              _Cont_Node_1{std::move(_result), std::move(a0), a1, a2});
          _stack.emplace_back(_Enter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<_Cont_Node_1>(_frame));
          std::shared_ptr<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          std::shared_ptr<tree> a2 = std::move(_f.a2);
          _result = f0(*a0, std::move(_f._tmp2), a1, *a2, std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, uint64_t &, tree &,
                                     T1 &>
    T1 tree_rect(T1 f, F1 &&f0) const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _Cont_Node: saves [a0, a1, a2], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Node {
        std::shared_ptr<tree> a0;
        uint64_t a1;
        std::shared_ptr<tree> a2;
      };

      /// _Cont_Node_1: saves [_tmp2, a0, a1, a2], resumes after recursive call,
      /// then processes rest.
      struct _Cont_Node_1 {
        T1 _tmp2;
        std::shared_ptr<tree> a0;
        uint64_t a1;
        std::shared_ptr<tree> a2;
      };

      using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified tree_rect: _Enter -> _Cont_Node -> _Cont_Node_1.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_Cont_Node{a0, a1, a2});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_Cont_Node>(_frame)) {
          auto _f = std::move(std::get<_Cont_Node>(_frame));
          std::shared_ptr<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          std::shared_ptr<tree> a2 = std::move(_f.a2);
          _stack.emplace_back(
              _Cont_Node_1{std::move(_result), std::move(a0), a1, a2});
          _stack.emplace_back(_Enter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<_Cont_Node_1>(_frame));
          std::shared_ptr<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          std::shared_ptr<tree> a2 = std::move(_f.a2);
          _result = f0(*a0, std::move(_f._tmp2), a1, *a2, std::move(_result));
        }
      }
      return _result;
    }
  };

  static inline const uint64_t test_tree_closures = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                        UINT64_C(20),
                        tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
    mylist<crane::fn<uint64_t(std::monostate)>> fns =
        std::move(t).tree_sum_closures();
    return sum_fns(std::move(fns));
  }();
  /// TEST 4: Each closure captures the tail AND the current value.
  /// After building all closures, call them — the captured lists
  /// must be independent copies.
  static mylist<crane::fn<uint64_t(uint64_t)>>
  build_accum_closures(const mylist<uint64_t> &l);
  static uint64_t apply_all(const mylist<crane::fn<uint64_t(uint64_t)>> &l,
                            uint64_t x);
  static inline const uint64_t test_accum_closures = []() {
    mylist<uint64_t> l = mylist<uint64_t>::mycons(
        UINT64_C(1),
        mylist<uint64_t>::mycons(
            UINT64_C(2),
            mylist<uint64_t>::mycons(UINT64_C(3), mylist<uint64_t>::mynil())));
    mylist<crane::fn<uint64_t(uint64_t)>> fns =
        build_accum_closures(std::move(l));
    return apply_all(std::move(fns), UINT64_C(0));
  }();
  static inline const uint64_t test_subtree_getters = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                        UINT64_C(20),
                        tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
    std::pair<crane::fn<uint64_t(std::monostate)>,
              crane::fn<uint64_t(std::monostate)>>
        p = std::move(t).make_subtree_getters();
    return (p.first(std::monostate{}) + p.second(std::monostate{}));
  }();
  /// TEST 6: Stress test — large list, each closure captures
  /// the entire remaining tail.
  static mylist<uint64_t> make_nat_list(uint64_t n);
  static inline const uint64_t test_stress_closures = []() {
    mylist<uint64_t> l = make_nat_list(UINT64_C(20));
    mylist<crane::fn<uint64_t(std::monostate)>> fns =
        build_len_closures(std::move(l));
    return sum_fns(std::move(fns));
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE7
