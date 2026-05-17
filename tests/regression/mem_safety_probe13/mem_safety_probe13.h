#ifndef INCLUDED_MEM_SAFETY_PROBE13
#define INCLUDED_MEM_SAFETY_PROBE13

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

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
      std::unique_ptr<tree> a0;
      uint64_t a1;
      std::unique_ptr<tree> a2;
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

    tree(const tree &_other) : v_(std::move(_other.clone().v_)) {}

    tree(tree &&_other) noexcept : v_(std::move(_other.v_)) {}

    tree &operator=(const tree &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    tree &operator=(tree &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    tree clone() const {
      tree _out{};

      struct _CloneFrame {
        const tree *_src;
        tree *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const tree *_src = _frame._src;
        tree *_dst = _frame._dst;
        if (std::holds_alternative<Leaf>(_src->v())) {
          _dst->v_ = Leaf{};
        } else {
          const auto &_alt = std::get<Node>(_src->v());
          _dst->v_ = Node{_alt.a0 ? std::make_unique<tree>() : nullptr, _alt.a1,
                          _alt.a2 ? std::make_unique<tree>() : nullptr};
          auto &_dst_alt = std::get<Node>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a2) {
            _stack.push_back({_alt.a2.get(), _dst_alt.a2.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static tree leaf() { return tree(Leaf{}); }

    static tree node(tree a0, uint64_t a1, tree a2) {
      return tree(Node{std::make_unique<tree>(std::move(a0)), a1,
                       std::make_unique<tree>(std::move(a2))});
    }

    // MANIPULATORS
    ~tree() {
      std::vector<std::unique_ptr<tree>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](tree &_node) {
        if (std::holds_alternative<Node>(_node.v_)) {
          auto &_alt = std::get<Node>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
          if (_alt.a2) {
            _stack.push_back(std::move(_alt.a2));
          }
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node) {
          _drain(*_node);
        }
      }
    }

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
          std::function<uint64_t(uint64_t)> f = [=](uint64_t n) mutable {
            return ((a2_value.tree_sum() + a20_value.tree_sum()) + n);
          };
          return (f(a10) + a00_value.tree_sum());
        }
      }
    }

    uint64_t tree_sum() const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _After_Node: saves [_s0, a1], dispatches next recursive call.
      struct _After_Node {
        tree *_s0;
        uint64_t a1;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        uint64_t _result;
        uint64_t a1;
      };

      using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
      uint64_t _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified tree_sum: _Enter -> _After_Node -> _Combine_Node.
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
            _stack.emplace_back(_After_Node{a0.get(), a1});
            _stack.emplace_back(_Enter{a2.get()});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{_result, _f.a1});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = ((_result + _f.a1) + _f._result);
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

      /// _After_Node: saves [_s0, a2, a1, a0], dispatches next recursive call.
      struct _After_Node {
        tree *_s0;
        tree a2;
        uint64_t a1;
        tree a0;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        T1 _result;
        tree a2;
        uint64_t a1;
        tree a0;
      };

      using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified tree_rec: _Enter -> _After_Node -> _Combine_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = std::move(f);
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_After_Node{a0.get(), *a2, a1, *a0});
            _stack.emplace_back(_Enter{a2.get()});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{_result, std::move(_f.a2), _f.a1,
                                            std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = f0(_f.a0, _result, _f.a1, _f.a2, _f._result);
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

      /// _After_Node: saves [_s0, a2, a1, a0], dispatches next recursive call.
      struct _After_Node {
        tree *_s0;
        tree a2;
        uint64_t a1;
        tree a0;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        T1 _result;
        tree a2;
        uint64_t a1;
        tree a0;
      };

      using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified tree_rect: _Enter -> _After_Node -> _Combine_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = std::move(f);
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_After_Node{a0.get(), *a2, a1, *a0});
            _stack.emplace_back(_Enter{a2.get()});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{_result, std::move(_f.a2), _f.a1,
                                            std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = f0(_f.a0, _result, _f.a1, _f.a2, _f._result);
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
      std::unique_ptr<mylist<A>> a1;
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

    mylist(const mylist<A> &_other) : v_(std::move(_other.clone().v_)) {}

    mylist(mylist<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

    mylist<A> &operator=(const mylist<A> &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    mylist<A> &operator=(mylist<A> &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    mylist<A> clone() const {
      mylist<A> _out{};

      struct _CloneFrame {
        const mylist<A> *_src;
        mylist<A> *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const mylist<A> *_src = _frame._src;
        mylist<A> *_dst = _frame._dst;
        if (std::holds_alternative<Mynil>(_src->v())) {
          _dst->v_ = Mynil{};
        } else {
          const auto &_alt = std::get<Mycons>(_src->v());
          _dst->v_ = Mycons{_alt.a0,
                            _alt.a1 ? std::make_unique<mylist<A>>() : nullptr};
          auto &_dst_alt = std::get<Mycons>(_dst->v_);
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    template <typename _U> explicit mylist(const mylist<_U> &_other) {
      if (std::holds_alternative<typename mylist<_U>::Mynil>(_other.v())) {
        this->v_ = Mynil{};
      } else {
        const auto &[a0, a1] =
            std::get<typename mylist<_U>::Mycons>(_other.v());
        this->v_ =
            Mycons{A(a0), a1 ? std::make_unique<mylist<A>>(*a1) : nullptr};
      }
    }

    static mylist<A> mynil() { return mylist(Mynil{}); }

    static mylist<A> mycons(A a0, mylist<A> a1) {
      return mylist(
          Mycons{std::move(a0), std::make_unique<mylist<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~mylist() {
      std::vector<std::unique_ptr<mylist<A>>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](mylist<A> &_node) {
        if (std::holds_alternative<Mycons>(_node.v_)) {
          auto &_alt = std::get<Mycons>(_node.v_);
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
          }
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node) {
          _drain(*_node);
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    mylist<A> app(mylist<A> l2) const {
      std::unique_ptr<mylist<A>> _head{};
      std::unique_ptr<mylist<A>> *_write = &_head;
      const mylist *_loop_self = this;
      mylist<A> _loop_l2 = std::move(l2);
      while (true) {
        auto &&_sv = *_loop_self;
        if (std::holds_alternative<typename mylist<A>::Mynil>(_sv.v())) {
          *_write = std::make_unique<mylist<A>>(std::move(_loop_l2));
          break;
        } else {
          const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(_sv.v());
          auto _cell = std::make_unique<mylist<A>>(
              typename mylist<A>::Mycons(a0, nullptr));
          *_write = std::move(_cell);
          _write = &std::get<typename mylist<A>::Mycons>((*_write)->v_mut()).a1;
          _loop_self = a1.get();
          continue;
        }
      }
      return std::move(*_head);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &>
    mylist<T1> map_list(F0 &&f) const {
      std::unique_ptr<mylist<T1>> _head{};
      std::unique_ptr<mylist<T1>> *_write = &_head;
      const mylist *_loop_self = this;
      while (true) {
        auto &&_sv = *_loop_self;
        if (std::holds_alternative<typename mylist<A>::Mynil>(_sv.v())) {
          *_write = std::make_unique<mylist<T1>>(mylist<T1>::mynil());
          break;
        } else {
          const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(_sv.v());
          auto _cell = std::make_unique<mylist<T1>>(
              typename mylist<T1>::Mycons(f(a0), nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename mylist<T1>::Mycons>((*_write)->v_mut()).a1;
          _loop_self = a1.get();
          continue;
        }
      }
      return std::move(*_head);
    }

    uint64_t length() const {
      const mylist *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const mylist *_self;
      };

      /// _Resume_Mycons: saves [_s0], resumes after recursive call with
      /// _result.
      struct _Resume_Mycons {
        decltype(UINT64_C(1)) _s0;
      };

      using _Frame = std::variant<_Enter, _Resume_Mycons>;
      uint64_t _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified length: _Enter -> _Resume_Mycons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const mylist *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename mylist<A>::Mynil>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1] =
                std::get<typename mylist<A>::Mycons>(_sv.v());
            _stack.emplace_back(_Resume_Mycons{UINT64_C(1)});
            _stack.emplace_back(_Enter{a1.get()});
          }
        } else {
          auto _f = std::move(std::get<_Resume_Mycons>(_frame));
          _result = (_f._s0 + _result);
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, mylist<A> &, T1 &>
    T1 mylist_rec(T1 f, F1 &&f0) const {
      const mylist *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const mylist *_self;
      };

      /// _Resume_Mycons: saves [f0, a1, a0], resumes after recursive call with
      /// _result.
      struct _Resume_Mycons {
        F1 f0;
        mylist<A> a1;
        A a0;
      };

      using _Frame = std::variant<_Enter, _Resume_Mycons>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified mylist_rec: _Enter -> _Resume_Mycons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const mylist *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename mylist<A>::Mynil>(_sv.v())) {
            _result = std::move(f);
          } else {
            const auto &[a0, a1] =
                std::get<typename mylist<A>::Mycons>(_sv.v());
            _stack.emplace_back(_Resume_Mycons{f0, *a1, a0});
            _stack.emplace_back(_Enter{a1.get()});
          }
        } else {
          auto _f = std::move(std::get<_Resume_Mycons>(_frame));
          _result = _f.f0(_f.a0, _f.a1, _result);
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, mylist<A> &, T1 &>
    T1 mylist_rect(T1 f, F1 &&f0) const {
      const mylist *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const mylist *_self;
      };

      /// _Resume_Mycons: saves [f0, a1, a0], resumes after recursive call with
      /// _result.
      struct _Resume_Mycons {
        F1 f0;
        mylist<A> a1;
        A a0;
      };

      using _Frame = std::variant<_Enter, _Resume_Mycons>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified mylist_rect: _Enter -> _Resume_Mycons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const mylist *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename mylist<A>::Mynil>(_sv.v())) {
            _result = std::move(f);
          } else {
            const auto &[a0, a1] =
                std::get<typename mylist<A>::Mycons>(_sv.v());
            _stack.emplace_back(_Resume_Mycons{f0, *a1, a0});
            _stack.emplace_back(_Enter{a1.get()});
          }
        } else {
          auto _f = std::move(std::get<_Resume_Mycons>(_frame));
          _result = _f.f0(_f.a0, _f.a1, _result);
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
  static std::pair<mylist<uint64_t>, mylist<std::function<uint64_t(uint64_t)>>>
  tree_vals_and_fns(const tree &t);
  static inline const uint64_t test_vals_and_fns = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                        UINT64_C(7),
                        tree::node(tree::leaf(), UINT64_C(11), tree::leaf()));
    auto _cs = tree_vals_and_fns(t);
    const mylist<uint64_t> &vals = _cs.first;
    const mylist<std::function<uint64_t(uint64_t)>> &fns = _cs.second;
    uint64_t val_sum = sum_list(vals);
    uint64_t fn_sum = sum_list(fns.template map_list<uint64_t>(
        [](std::function<uint64_t(uint64_t)> f) { return f(UINT64_C(0)); }));
    return (val_sum + fn_sum);
  }();
  static inline const uint64_t test_double_match = []() {
    tree t = tree::node(
        tree::node(tree::node(tree::leaf(), UINT64_C(1), tree::leaf()),
                   UINT64_C(2),
                   tree::node(tree::leaf(), UINT64_C(3), tree::leaf())),
        UINT64_C(10), tree::node(tree::leaf(), UINT64_C(20), tree::leaf()));
    return std::move(t).double_match();
  }();
  /// TEST 4: Deeply nested tree with closures at EVERY level.
  /// Each closure captures values from its level AND from the parent.
  /// Tests stack depth and closure lifetime with deep nesting.
  static tree make_deep(uint64_t n);
  static mylist<std::function<uint64_t(uint64_t)>>
  depth_fns(const tree &t, uint64_t parent_val);
  static inline const uint64_t test_depth_fns = []() {
    tree t = make_deep(UINT64_C(5));
    mylist<std::function<uint64_t(uint64_t)>> fns =
        depth_fns(std::move(t), UINT64_C(0));
    return sum_list(std::move(fns).template map_list<uint64_t>(
        [](std::function<uint64_t(uint64_t)> f) { return f(UINT64_C(0)); }));
  }();

  /// TEST 5: Transform a tree by replacing each value with a
  /// function, then evaluate. Tests closures in recursive
  /// tree transformation.
  struct ftree {
    // TYPES
    struct FLeaf {};

    struct FNode {
      std::unique_ptr<ftree> a0;
      std::function<uint64_t(uint64_t)> a1;
      std::unique_ptr<ftree> a2;
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

    ftree(const ftree &_other) : v_(std::move(_other.clone().v_)) {}

    ftree(ftree &&_other) noexcept : v_(std::move(_other.v_)) {}

    ftree &operator=(const ftree &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    ftree &operator=(ftree &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    ftree clone() const {
      ftree _out{};

      struct _CloneFrame {
        const ftree *_src;
        ftree *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const ftree *_src = _frame._src;
        ftree *_dst = _frame._dst;
        if (std::holds_alternative<FLeaf>(_src->v())) {
          _dst->v_ = FLeaf{};
        } else {
          const auto &_alt = std::get<FNode>(_src->v());
          _dst->v_ =
              FNode{_alt.a0 ? std::make_unique<ftree>() : nullptr, _alt.a1,
                    _alt.a2 ? std::make_unique<ftree>() : nullptr};
          auto &_dst_alt = std::get<FNode>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a2) {
            _stack.push_back({_alt.a2.get(), _dst_alt.a2.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static ftree fleaf() { return ftree(FLeaf{}); }

    static ftree fnode(ftree a0, std::function<uint64_t(uint64_t)> a1,
                       ftree a2) {
      return ftree(FNode{std::make_unique<ftree>(std::move(a0)), std::move(a1),
                         std::make_unique<ftree>(std::move(a2))});
    }

    // MANIPULATORS
    ~ftree() {
      std::vector<std::unique_ptr<ftree>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](ftree &_node) {
        if (std::holds_alternative<FNode>(_node.v_)) {
          auto &_alt = std::get<FNode>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
          if (_alt.a2) {
            _stack.push_back(std::move(_alt.a2));
          }
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node) {
          _drain(*_node);
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t eval_ftree(uint64_t base) const {
      const ftree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const ftree *_self;
      };

      /// _After_FNode: saves [_s0, base], dispatches next recursive call.
      struct _After_FNode {
        ftree *_s0;
        uint64_t base;
      };

      /// _Combine_FNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_FNode {
        uint64_t _result;
        uint64_t base;
      };

      using _Frame = std::variant<_Enter, _After_FNode, _Combine_FNode>;
      uint64_t _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified eval_ftree: _Enter -> _After_FNode -> _Combine_FNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const ftree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ftree::FLeaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2] = std::get<typename ftree::FNode>(_sv.v());
            _stack.emplace_back(_After_FNode{a0.get(), a1(base)});
            _stack.emplace_back(_Enter{a2.get()});
          }
        } else if (std::holds_alternative<_After_FNode>(_frame)) {
          auto _f = std::move(std::get<_After_FNode>(_frame));
          _stack.emplace_back(_Combine_FNode{_result, _f.base});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_FNode>(_frame));
          _result = ((_result + _f.base) + _f._result);
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, ftree &, T1 &,
                                     std::function<uint64_t(uint64_t)> &,
                                     ftree &, T1 &>
    T1 ftree_rec(T1 f, F1 &&f0) const {
      const ftree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const ftree *_self;
      };

      /// _After_FNode: saves [_s0, a2, a1, a0], dispatches next recursive call.
      struct _After_FNode {
        ftree *_s0;
        ftree a2;
        std::function<uint64_t(uint64_t)> a1;
        ftree a0;
      };

      /// _Combine_FNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_FNode {
        T1 _result;
        ftree a2;
        std::function<uint64_t(uint64_t)> a1;
        ftree a0;
      };

      using _Frame = std::variant<_Enter, _After_FNode, _Combine_FNode>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified ftree_rec: _Enter -> _After_FNode -> _Combine_FNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const ftree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ftree::FLeaf>(_sv.v())) {
            _result = std::move(f);
          } else {
            const auto &[a0, a1, a2] = std::get<typename ftree::FNode>(_sv.v());
            _stack.emplace_back(
                _After_FNode{a0.get(), *a2, std::move(a1), *a0});
            _stack.emplace_back(_Enter{a2.get()});
          }
        } else if (std::holds_alternative<_After_FNode>(_frame)) {
          auto _f = std::move(std::get<_After_FNode>(_frame));
          _stack.emplace_back(_Combine_FNode{
              _result, std::move(_f.a2), std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_FNode>(_frame));
          _result = f0(_f.a0, _result, _f.a1, _f.a2, _f._result);
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, ftree &, T1 &,
                                     std::function<uint64_t(uint64_t)> &,
                                     ftree &, T1 &>
    T1 ftree_rect(T1 f, F1 &&f0) const {
      const ftree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const ftree *_self;
      };

      /// _After_FNode: saves [_s0, a2, a1, a0], dispatches next recursive call.
      struct _After_FNode {
        ftree *_s0;
        ftree a2;
        std::function<uint64_t(uint64_t)> a1;
        ftree a0;
      };

      /// _Combine_FNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_FNode {
        T1 _result;
        ftree a2;
        std::function<uint64_t(uint64_t)> a1;
        ftree a0;
      };

      using _Frame = std::variant<_Enter, _After_FNode, _Combine_FNode>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified ftree_rect: _Enter -> _After_FNode -> _Combine_FNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const ftree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ftree::FLeaf>(_sv.v())) {
            _result = std::move(f);
          } else {
            const auto &[a0, a1, a2] = std::get<typename ftree::FNode>(_sv.v());
            _stack.emplace_back(
                _After_FNode{a0.get(), *a2, std::move(a1), *a0});
            _stack.emplace_back(_Enter{a2.get()});
          }
        } else if (std::holds_alternative<_After_FNode>(_frame)) {
          auto _f = std::move(std::get<_After_FNode>(_frame));
          _stack.emplace_back(_Combine_FNode{
              _result, std::move(_f.a2), std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_FNode>(_frame));
          _result = f0(_f.a0, _result, _f.a1, _f.a2, _f._result);
        }
      }
      return _result;
    }
  };

  static ftree tree_to_ftree(const tree &t);
  static inline const uint64_t test_ftree = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                        UINT64_C(7),
                        tree::node(tree::leaf(), UINT64_C(11), tree::leaf()));
    ftree ft = tree_to_ftree(std::move(t));
    return std::move(ft).eval_ftree(UINT64_C(100));
  }();
  /// TEST 6: Flatten a tree of lists into a single list,
  /// where each list element is a closure.
  static mylist<std::function<uint64_t(uint64_t)>>
  flatten_tree_fns(const tree &t);
  static inline const uint64_t test_flatten_fns = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                        UINT64_C(7),
                        tree::node(tree::leaf(), UINT64_C(11), tree::leaf()));
    mylist<std::function<uint64_t(uint64_t)>> fns =
        flatten_tree_fns(std::move(t));
    return sum_list(std::move(fns).template map_list<uint64_t>(
        [](std::function<uint64_t(uint64_t)> f) { return f(UINT64_C(1)); }));
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE13
