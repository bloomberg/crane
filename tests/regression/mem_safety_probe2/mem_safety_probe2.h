#ifndef INCLUDED_MEM_SAFETY_PROBE2
#define INCLUDED_MEM_SAFETY_PROBE2

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MemSafetyProbe2 {
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
        std::function<uint64_t(uint64_t)> f = [&](uint64_t _x0) -> uint64_t {
          return a0->sum_values(_x0);
        };
        return (f(a1) + a2->sum_values(a1));
      }
    }

    /// TEST 15: Multiple closures applied in sequence, each consuming a tree.
    uint64_t apply_chain(tree t2, const tree &t3, uint64_t x) const {
      std::function<uint64_t(uint64_t)> f1 = [&](uint64_t _x0) -> uint64_t {
        return std::move(*this).sum_values(_x0);
      };
      std::function<uint64_t(uint64_t)> f2 = [&](uint64_t _x0) -> uint64_t {
        return std::move(t2).sum_values(_x0);
      };
      return t3.sum_values(f2(f1(x)));
    }

    /// TEST 14: Partial application stored in pair alongside tree.
    std::pair<std::function<uint64_t(uint64_t)>, tree>
    pair_closure_tree() const {
      tree _self_val = *this;
      return std::make_pair(
          [=](uint64_t _x0) mutable -> uint64_t {
            return _self_val.sum_values(_x0);
          },
          *this);
    }

    /// TEST 12: Value type cloned into pair, then both halves used with
    /// closures.
    uint64_t clone_and_close() const {
      std::pair<tree, tree> p = std::make_pair(*this, *this);
      std::function<uint64_t(uint64_t)> f =
          [=](uint64_t _x0) mutable -> uint64_t {
        return p.first.sum_values(_x0);
      };
      std::function<uint64_t(uint64_t)> g = [&](uint64_t _x0) -> uint64_t {
        return p.second.sum_values(_x0);
      };
      return (f(UINT64_C(1)) + g(UINT64_C(2)));
    }

    /// TEST 11: Partial application used in BOTH branches of a match
    /// (only one branch executes).
    uint64_t branch_use(bool b) const {
      std::function<uint64_t(uint64_t)> f = [&](uint64_t _x0) -> uint64_t {
        return std::move(*this).sum_values(_x0);
      };
      if (b) {
        return f(UINT64_C(0));
      } else {
        return f(UINT64_C(100));
      }
    }

    /// TEST 9: Option wrapping a closure.
    std::optional<std::function<uint64_t(uint64_t)>> opt_adder(bool b) const {
      tree _self_val = *this;
      if (b) {
        return std::make_optional<std::function<uint64_t(uint64_t)>>(
            [=](uint64_t _x0) mutable -> uint64_t {
              return _self_val.sum_values(_x0);
            });
      } else {
        return std::optional<std::function<uint64_t(uint64_t)>>();
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
        std::function<uint64_t(uint64_t)> fl = [&](uint64_t _x0) -> uint64_t {
          return a0->sum_values(_x0);
        };
        std::function<uint64_t(uint64_t)> fr = [&](uint64_t _x0) -> uint64_t {
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
      std::function<uint64_t(uint64_t)> f = [&](uint64_t _x0) -> uint64_t {
        return std::move(*this).sum_values(_x0);
      };
      return (f(x) + x);
    }

    /// TEST 4: Partial application of a wrapper that stores its arg in a
    /// constructor.
    tree make_node(uint64_t v, tree r) const {
      return tree::node(std::move(*this), v, std::move(r));
    }

    /// TEST 3: Compose two closures, each capturing a different tree.
    uint64_t compose_adders(const tree &t2, uint64_t x) const {
      return this->sum_values(t2.sum_values(x));
    }

    /// TEST 2: CPS-style: pass a continuation that captures value types.
    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &,
                                     std::function<uint64_t(uint64_t)> &>
    T1 with_tree(F0 &&k) const {
      tree _self_val = *this;
      return k([=](uint64_t _x0) mutable -> uint64_t {
        return _self_val.sum_values(_x0);
      });
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

    mylist<A> myrev() const { return this->myrev_append(mylist<A>::mynil()); }

    /// TEST 17: Build a list of closures, reverse it, and apply all.
    /// Probes whether closures survive list operations.
    mylist<A> myrev_append(mylist<A> acc) const {
      mylist<A> _result;
      const mylist *_loop_self = this;
      mylist<A> _loop_acc = std::move(acc);
      while (true) {
        auto &&_sv = *_loop_self;
        if (std::holds_alternative<typename mylist<A>::Mynil>(_sv.v())) {
          _result = std::move(_loop_acc);
          break;
        } else {
          const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(_sv.v());
          _loop_self = a1.get();
          _loop_acc = mylist<A>::mycons(a0, std::move(_loop_acc));
        }
      }
      return _result;
    }

    uint64_t mylength() const {
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
      /// Loopified mylength: _Enter -> _Resume_Mycons.
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

  static inline const uint64_t test_dup_tree = []() {
    tree t = tree::node(tree::leaf(), UINT64_C(42), tree::leaf());
    std::pair<tree, uint64_t> p = std::move(t).dup_tree();
    return (p.first.sum_values(UINT64_C(0)) + p.second);
  }();
  static inline const uint64_t test_cps = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                        UINT64_C(20),
                        tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
    return std::move(t).template with_tree<uint64_t>(
        [](std::function<uint64_t(uint64_t)> f) {
          return (f(UINT64_C(5)) + f(UINT64_C(0)));
        });
  }();
  static inline const uint64_t test_compose = []() {
    tree t1 = tree::node(tree::leaf(), UINT64_C(10), tree::leaf());
    tree t2 = tree::node(tree::leaf(), UINT64_C(20), tree::leaf());
    return std::move(t1).compose_adders(std::move(t2), UINT64_C(5));
  }();
  static inline const uint64_t test_partial_ctor = []() {
    return []() {
      tree t = tree::node(tree::leaf(), UINT64_C(42), tree::leaf());
      std::function<tree(uint64_t, tree)> f = [&](uint64_t _x0,
                                                  tree _x1) -> tree {
        return std::move(t).make_node(_x0, _x1);
      };
      tree t2 = f(UINT64_C(99), tree::leaf());
      return std::move(t2).sum_values(UINT64_C(0));
    }();
  }();
  static inline const uint64_t test_double_wrap = []() {
    tree t = tree::node(tree::leaf(), UINT64_C(42), tree::leaf());
    return std::move(t).double_wrap(UINT64_C(10));
  }();
  static inline const uint64_t test_tree_pair = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                        UINT64_C(20),
                        tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
    std::pair<tree, tree> p = std::move(t).tree_pair();
    return (p.first.sum_values(UINT64_C(0)) + p.second.sum_values(UINT64_C(0)));
  }();
  /// TEST 7: Closure escaping through a list, then applied.
  static mylist<uint64_t>
  map_apply(const mylist<std::function<uint64_t(uint64_t)>> &fs, uint64_t x);
  static uint64_t mysum(const mylist<uint64_t> &l);
  static inline const uint64_t test_closure_escape_list = []() {
    return []() {
      tree t1 = tree::node(tree::leaf(), UINT64_C(10), tree::leaf());
      tree t2 = tree::node(tree::leaf(), UINT64_C(20), tree::leaf());
      mylist<std::function<uint64_t(uint64_t)>> fs =
          mylist<std::function<uint64_t(uint64_t)>>::mycons(
              [=](uint64_t _x0) mutable -> uint64_t {
                return t1.sum_values(_x0);
              },
              mylist<std::function<uint64_t(uint64_t)>>::mycons(
                  [=](uint64_t _x0) mutable -> uint64_t {
                    return t2.sum_values(_x0);
                  },
                  mylist<std::function<uint64_t(uint64_t)>>::mynil()));
      return mysum(map_apply(std::move(fs), UINT64_C(5)));
    }();
  }();
  static inline const uint64_t test_extract_apply =
      tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                 UINT64_C(20),
                 tree::node(tree::leaf(), UINT64_C(30), tree::leaf()))
          .extract_and_apply();
  static inline const uint64_t test_opt_closure = []() {
    tree t = tree::node(tree::leaf(), UINT64_C(42), tree::leaf());
    auto _cs = t.opt_adder(true);
    if (_cs.has_value()) {
      const std::function<uint64_t(uint64_t)> &f = *_cs;
      return f(UINT64_C(10));
    } else {
      return UINT64_C(0);
    }
  }();
  /// TEST 10: Two partial applications of the SAME function
  /// with DIFFERENT captured values. Both must independently own data.
  static inline const uint64_t test_two_partial = []() {
    return []() {
      tree t1 = tree::node(tree::leaf(), UINT64_C(10), tree::leaf());
      tree t2 = tree::node(tree::leaf(), UINT64_C(20), tree::leaf());
      std::function<uint64_t(uint64_t)> f = [&](uint64_t _x0) -> uint64_t {
        return std::move(t1).sum_values(_x0);
      };
      std::function<uint64_t(uint64_t)> g = [&](uint64_t _x0) -> uint64_t {
        return std::move(t2).sum_values(_x0);
      };
      return f(g(UINT64_C(0)));
    }();
  }();
  static inline const uint64_t test_branch_true =
      tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                 UINT64_C(20),
                 tree::node(tree::leaf(), UINT64_C(30), tree::leaf()))
          .branch_use(true);
  /// f 0 = 60
  static inline const uint64_t test_branch_false =
      tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                 UINT64_C(20),
                 tree::node(tree::leaf(), UINT64_C(30), tree::leaf()))
          .branch_use(false);
  /// With t = Node Leaf 42 Leaf: 43 + 44 = 87
  static inline const uint64_t test_clone_close =
      tree::node(tree::leaf(), UINT64_C(42), tree::leaf()).clone_and_close();
  /// TEST 13: Fold building tree from closures' results.
  static tree
  fold_tree_build(const mylist<std::function<uint64_t(uint64_t)>> &fs,
                  uint64_t acc);
  static inline const uint64_t test_fold_tree = []() {
    return []() {
      tree t1 = tree::node(tree::leaf(), UINT64_C(10), tree::leaf());
      tree t2 = tree::node(tree::leaf(), UINT64_C(20), tree::leaf());
      mylist<std::function<uint64_t(uint64_t)>> fs =
          mylist<std::function<uint64_t(uint64_t)>>::mycons(
              [=](uint64_t _x0) mutable -> uint64_t {
                return t1.sum_values(_x0);
              },
              mylist<std::function<uint64_t(uint64_t)>>::mycons(
                  [=](uint64_t _x0) mutable -> uint64_t {
                    return t2.sum_values(_x0);
                  },
                  mylist<std::function<uint64_t(uint64_t)>>::mynil()));
      tree result = fold_tree_build(std::move(fs), UINT64_C(5));
      return std::move(result).sum_values(UINT64_C(0));
    }();
  }();
  static inline const uint64_t test_pair_closure_tree = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                        UINT64_C(20),
                        tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
    std::pair<std::function<uint64_t(uint64_t)>, tree> p =
        std::move(t).pair_closure_tree();
    return (p.first(UINT64_C(5)) + p.second.sum_values(UINT64_C(0)));
  }();
  static inline const uint64_t test_chain =
      tree::node(tree::leaf(), UINT64_C(10), tree::leaf())
          .apply_chain(tree::node(tree::leaf(), UINT64_C(20), tree::leaf()),
                       tree::node(tree::leaf(), UINT64_C(30), tree::leaf()),
                       UINT64_C(5));
  static inline const uint64_t test_capture_branch =
      tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                 UINT64_C(20),
                 tree::node(tree::leaf(), UINT64_C(30), tree::leaf()))
          .capture_in_branch(tree::leaf());
  static uint64_t apply_all(const mylist<std::function<uint64_t(uint64_t)>> &fs,
                            uint64_t x);
  static inline const uint64_t test_rev_closures = []() {
    return []() {
      tree t1 = tree::node(tree::leaf(), UINT64_C(10), tree::leaf());
      tree t2 = tree::node(tree::leaf(), UINT64_C(20), tree::leaf());
      tree t3 = tree::node(tree::leaf(), UINT64_C(30), tree::leaf());
      mylist<std::function<uint64_t(uint64_t)>> fs =
          mylist<std::function<uint64_t(uint64_t)>>::mycons(
              [=](uint64_t _x0) mutable -> uint64_t {
                return t1.sum_values(_x0);
              },
              mylist<std::function<uint64_t(uint64_t)>>::mycons(
                  [=](uint64_t _x0) mutable -> uint64_t {
                    return t2.sum_values(_x0);
                  },
                  mylist<std::function<uint64_t(uint64_t)>>::mycons(
                      [=](uint64_t _x0) mutable -> uint64_t {
                        return t3.sum_values(_x0);
                      },
                      mylist<std::function<uint64_t(uint64_t)>>::mynil())));
      mylist<std::function<uint64_t(uint64_t)>> rfs = std::move(fs).myrev();
      return apply_all(std::move(rfs), UINT64_C(5));
    }();
  }();
  static inline const uint64_t test_build_from_partial = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                        UINT64_C(20),
                        tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
    tree t2 = std::move(t).build_from_partial();
    return std::move(t2).sum_values(UINT64_C(0));
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE2
