#ifndef INCLUDED_MEM_SAFETY_PROBE9
#define INCLUDED_MEM_SAFETY_PROBE9

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MemSafetyProbe9 {
  /// These tests probe patterns where closures accumulate
  /// during tree traversal. Each closure captures subtrees
  /// (unique_ptr fields) that are also used in recursive calls.
  /// The captures must be independent clones.
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
          _dst->v_ = Node{_alt.a0 ? std::make_shared<tree>() : nullptr, _alt.a1,
                          _alt.a2 ? std::make_shared<tree>() : nullptr};
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
      return tree(Node{std::make_shared<tree>(std::move(a0)), a1,
                       std::make_shared<tree>(std::move(a2))});
    }

    // MANIPULATORS
    ~tree() {
      std::vector<std::shared_ptr<tree>> _stack{};
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

    /// TEST 5: Mutual use pattern — the left subtree is used to compute
    /// a value that's passed to a closure that captures the right subtree.
    uint64_t cross_capture() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        const tree &a0_value = *a0;
        const tree &a2_value = *a2;
        uint64_t lsum = a0_value.tree_sum();
        std::function<uint64_t(uint64_t)> f = [=](uint64_t n) mutable {
          return (a2_value.tree_sum() + n);
        };
        return (f(lsum) + f(a1));
      }
    }

    /// TEST 4: Closures that capture a tree AND its subtrees
    /// independently — tests that cloning produces independent
    /// copies. Modify one subtree's computation after capture.
    uint64_t triple_capture() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return UINT64_C(0);
      } else {
        auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return ((_anon_f1(UINT64_C(0), *a0) + _anon_f2(UINT64_C(0), *a2)) +
                _anon_f3(UINT64_C(0), *this));
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
          _result = ((std::move(_result) + _f.a1) + std::move(_f._result));
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
          _stack.emplace_back(_Combine_Node{
              std::move(_result), std::move(_f.a2), _f.a1, std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = f0(_f.a0, std::move(_result), _f.a1, _f.a2,
                       std::move(_f._result));
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
          _stack.emplace_back(_Combine_Node{
              std::move(_result), std::move(_f.a2), _f.a1, std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = f0(_f.a0, std::move(_result), _f.a1, _f.a2,
                       std::move(_f._result));
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
                            _alt.a1 ? std::make_shared<mylist<A>>() : nullptr};
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
            Mycons{A(a0), a1 ? std::make_shared<mylist<A>>(*a1) : nullptr};
      }
    }

    static mylist<A> mynil() { return mylist(Mynil{}); }

    static mylist<A> mycons(A a0, mylist<A> a1) {
      return mylist(
          Mycons{std::move(a0), std::make_shared<mylist<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~mylist() {
      std::vector<std::shared_ptr<mylist<A>>> _stack{};
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

  template <typename T1> static uint64_t _anon_f1(const T1, const tree l) {
    return l.tree_sum();
  }

  template <typename T1> static uint64_t _anon_f2(const T1, const tree r) {
    return std::move(r).tree_sum();
  }

  template <typename T1> static uint64_t _anon_f3(const T1, const tree t) {
    return t.tree_sum();
  }

  static uint64_t sum_fns(const mylist<std::function<uint64_t(uint64_t)>> &l);

  /// TEST 1: Collect closures that each capture a subtree.
  /// Both l and r are captured AND used in recursive calls.
  template <typename T1>
  static uint64_t _collect_subtree_sums_f(const T1, const tree l,
                                          const uint64_t v, const tree r) {
    return ((std::move(l).tree_sum() + v) + r.tree_sum());
  }

  static mylist<std::function<uint64_t(uint64_t)>>
  collect_subtree_sums(const tree &t,
                       mylist<std::function<uint64_t(uint64_t)>> acc);
  static inline const uint64_t test_collect = []() {
    tree t = tree::node(
        tree::node(tree::leaf(), UINT64_C(5), tree::leaf()), UINT64_C(10),
        tree::node(tree::leaf(), UINT64_C(15),
                   tree::node(tree::leaf(), UINT64_C(20), tree::leaf())));
    mylist<std::function<uint64_t(uint64_t)>> fns = collect_subtree_sums(
        std::move(t), mylist<std::function<uint64_t(uint64_t)>>::mynil());
    return sum_fns(std::move(fns));
  }();

  /// TEST 2: Similar but each closure captures ONLY the left subtree.
  /// The left subtree is shared between closure and recursive call.
  template <typename T1>
  static uint64_t _collect_left_sums_f(const T1, const tree l) {
    return std::move(l).tree_sum();
  }

  static mylist<std::function<uint64_t(uint64_t)>>
  collect_left_sums(const tree &t,
                    mylist<std::function<uint64_t(uint64_t)>> acc);
  static inline const uint64_t test_left_sums = []() {
    tree t = tree::node(
        tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                   UINT64_C(7), tree::leaf()),
        UINT64_C(10), tree::node(tree::leaf(), UINT64_C(15), tree::leaf()));
    mylist<std::function<uint64_t(uint64_t)>> fns = collect_left_sums(
        std::move(t), mylist<std::function<uint64_t(uint64_t)>>::mynil());
    return sum_fns(std::move(fns));
  }();

  /// TEST 3: Build closures from list where each closure
  /// captures the tail and a computed value.
  template <typename T1>
  static uint64_t _list_accum_closures_f(const T1, const uint64_t x,
                                         const uint64_t tail_len) {
    return (std::move(x) * tail_len);
  }

  static mylist<std::function<uint64_t(uint64_t)>>
  list_accum_closures(const mylist<uint64_t> &l,
                      mylist<std::function<uint64_t(uint64_t)>> acc);
  static inline const uint64_t test_list_accum = []() {
    mylist<uint64_t> l = mylist<uint64_t>::mycons(
        UINT64_C(10),
        mylist<uint64_t>::mycons(
            UINT64_C(20),
            mylist<uint64_t>::mycons(UINT64_C(30), mylist<uint64_t>::mynil())));
    mylist<std::function<uint64_t(uint64_t)>> fns = list_accum_closures(
        std::move(l), mylist<std::function<uint64_t(uint64_t)>>::mynil());
    return sum_fns(std::move(fns));
  }();
  static inline const uint64_t test_triple =
      tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                 UINT64_C(20),
                 tree::node(tree::leaf(), UINT64_C(30), tree::leaf()))
          .triple_capture();
  static inline const uint64_t test_cross =
      tree::node(tree::node(tree::leaf(), UINT64_C(5), tree::leaf()),
                 UINT64_C(10),
                 tree::node(tree::leaf(), UINT64_C(15), tree::leaf()))
          .cross_capture();
  /// TEST 6: Stress test — large tree, many closures.
  static tree make_balanced(uint64_t n);
  static inline const uint64_t test_stress = []() {
    tree t = make_balanced(UINT64_C(5));
    mylist<std::function<uint64_t(uint64_t)>> fns = collect_left_sums(
        std::move(t), mylist<std::function<uint64_t(uint64_t)>>::mynil());
    return sum_fns(std::move(fns));
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE9
