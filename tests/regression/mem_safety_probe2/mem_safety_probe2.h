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
      std::unique_ptr<tree> d_a0;
      unsigned int d_a1;
      std::unique_ptr<tree> d_a2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Leaf _v) : d_v_(_v) {}

    explicit tree(Node _v) : d_v_(std::move(_v)) {}

    tree(const tree &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    tree(tree &&_other) : d_v_(std::move(_other.d_v_)) {}

    tree &operator=(const tree &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    tree &operator=(tree &&_other) {
      d_v_ = std::move(_other.d_v_);
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
          _dst->d_v_ = Leaf{};
        } else {
          const auto &_alt = std::get<Node>(_src->v());
          _dst->d_v_ =
              Node{_alt.d_a0 ? std::make_unique<tree>() : nullptr, _alt.d_a1,
                   _alt.d_a2 ? std::make_unique<tree>() : nullptr};
          auto &_dst_alt = std::get<Node>(_dst->d_v_);
          if (_alt.d_a0) {
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          }
          if (_alt.d_a2) {
            _stack.push_back({_alt.d_a2.get(), _dst_alt.d_a2.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static tree leaf() { return tree(Leaf{}); }

    static tree node(tree a0, unsigned int a1, tree a2) {
      return tree(Node{std::make_unique<tree>(std::move(a0)), std::move(a1),
                       std::make_unique<tree>(std::move(a2))});
    }

    // MANIPULATORS
    ~tree() {
      std::vector<std::unique_ptr<tree>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](tree &_node) {
        if (std::holds_alternative<Node>(_node.d_v_)) {
          auto &_alt = std::get<Node>(_node.d_v_);
          if (_alt.d_a0) {
            _stack.push_back(std::move(_alt.d_a0));
          }
          if (_alt.d_a2) {
            _stack.push_back(std::move(_alt.d_a2));
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

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }

    /// TEST 18: Construct a tree using partial app results, then traverse it.
    tree build_from_partial() const {
      unsigned int v = (*(this)).sum_values(0u);
      return tree::node(tree::node(tree::leaf(), v, tree::leaf()), v,
                        tree::node(tree::leaf(), v, tree::leaf()));
    }

    /// TEST 16: Closure captured in a match branch that also destructs a tree.
    /// The closure captures a value-type match-bound field.
    unsigned int capture_in_branch(const tree &) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        return 0u;
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(_sv.v());
        std::function<unsigned int(unsigned int)> f =
            [&](unsigned int _x0) -> unsigned int {
          return (*(d_a0)).sum_values(_x0);
        };
        return (f(d_a1) + (*(d_a2)).sum_values(d_a1));
      }
    }

    /// TEST 15: Multiple closures applied in sequence, each consuming a tree.
    unsigned int apply_chain(tree t2, const tree &t3,
                             const unsigned int x) const {
      std::function<unsigned int(unsigned int)> f1 =
          [&](unsigned int _x0) -> unsigned int {
        return std::move(*(this)).sum_values(_x0);
      };
      std::function<unsigned int(unsigned int)> f2 =
          [&](unsigned int _x0) -> unsigned int {
        return std::move(t2).sum_values(_x0);
      };
      return t3.sum_values(f2(f1(x)));
    }

    /// TEST 14: Partial application stored in pair alongside tree.
    std::pair<std::function<unsigned int(unsigned int)>, tree>
    pair_closure_tree() const {
      tree _self_val = *(this);
      return std::make_pair(
          [=](unsigned int _x0) mutable -> unsigned int {
            return _self_val.sum_values(_x0);
          },
          *(this));
    }

    /// TEST 12: Value type cloned into pair, then both halves used with
    /// closures.
    unsigned int clone_and_close() const {
      std::pair<tree, tree> p = std::make_pair(*(this), *(this));
      std::function<unsigned int(unsigned int)> f =
          [=](unsigned int _x0) mutable -> unsigned int {
        return p.first.sum_values(_x0);
      };
      std::function<unsigned int(unsigned int)> g =
          [&](unsigned int _x0) -> unsigned int {
        return p.second.sum_values(_x0);
      };
      return (f(1u) + g(2u));
    }

    /// TEST 11: Partial application used in BOTH branches of a match
    /// (only one branch executes).
    unsigned int branch_use(const bool b) const {
      std::function<unsigned int(unsigned int)> f =
          [&](unsigned int _x0) -> unsigned int {
        return std::move(*(this)).sum_values(_x0);
      };
      if (b) {
        return f(0u);
      } else {
        return f(100u);
      }
    }

    /// TEST 9: Option wrapping a closure.
    std::optional<std::function<unsigned int(unsigned int)>>
    opt_adder(const bool b) const {
      tree _self_val = *(this);
      if (b) {
        return std::make_optional<std::function<unsigned int(unsigned int)>>(
            [=](unsigned int _x0) mutable -> unsigned int {
              return _self_val.sum_values(_x0);
            });
      } else {
        return std::optional<std::function<unsigned int(unsigned int)>>();
      }
    }

    /// TEST 8: Match inside let-in where the partial application captures
    /// a match-bound field AND the match is inside a let continuation.
    /// Probes interaction between escape analysis and nested match.
    unsigned int extract_and_apply() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        return 0u;
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(_sv.v());
        std::function<unsigned int(unsigned int)> fl =
            [&](unsigned int _x0) -> unsigned int {
          return (*(d_a0)).sum_values(_x0);
        };
        std::function<unsigned int(unsigned int)> fr =
            [&](unsigned int _x0) -> unsigned int {
          return (*(d_a2)).sum_values(_x0);
        };
        return (fl(d_a1) + fr(d_a1));
      }
    }

    /// TEST 6: Value type used twice in pair.
    std::pair<tree, tree> tree_pair() const {
      return std::make_pair(*(this), *(this));
    }

    /// TEST 5: Closure capturing a closure.
    /// The inner closure captures a tree, the outer captures the inner closure.
    unsigned int double_wrap(const unsigned int x) const {
      std::function<unsigned int(unsigned int)> f =
          [&](unsigned int _x0) -> unsigned int {
        return std::move(*(this)).sum_values(_x0);
      };
      return (f(x) + x);
    }

    /// TEST 4: Partial application of a wrapper that stores its arg in a
    /// constructor.
    tree make_node(const unsigned int v, tree r) const {
      return tree::node(std::move(*(this)), v, std::move(r));
    }

    /// TEST 3: Compose two closures, each capturing a different tree.
    unsigned int compose_adders(const tree &t2, const unsigned int x) const {
      return (*(this)).sum_values(t2.sum_values(x));
    }

    /// TEST 2: CPS-style: pass a continuation that captures value types.
    template <typename T1, typename F0>
      requires std::is_invocable_r_v<
          T1, F0 &, std::function<unsigned int(unsigned int)> &>
    T1 with_tree(F0 &&k) const {
      tree _self_val = *(this);
      return k([=](unsigned int _x0) mutable -> unsigned int {
        return _self_val.sum_values(_x0);
      });
    }

    /// TEST 1: Use value type in both a partial application AND as a
    /// constructor arg. Tests whether the move analysis correctly handles
    /// double-use.
    std::pair<tree, unsigned int> dup_tree() const {
      return std::make_pair(tree::node(*(this), 0u, tree::leaf()),
                            (*(this)).sum_values(0u));
    }

    unsigned int sum_values(const unsigned int x) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        return x;
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(_sv.v());
        auto &&_sv0 = *(d_a0);
        if (std::holds_alternative<typename tree::Leaf>(_sv0.v())) {
          return (d_a1 + x);
        } else {
          const auto &[d_a00, d_a10, d_a20] =
              std::get<typename tree::Node>(_sv0.v());
          auto &&_sv1 = *(d_a2);
          if (std::holds_alternative<typename tree::Leaf>(_sv1.v())) {
            return (d_a10 + x);
          } else {
            const auto &[d_a01, d_a11, d_a21] =
                std::get<typename tree::Node>(_sv1.v());
            return (((d_a10 + d_a11) + d_a1) + x);
          }
        }
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, unsigned int &,
                                     tree &, T1 &>
    T1 tree_rec(T1 f, F1 &&f0) const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _After_Node: saves [_s0, d_a2, d_a1, d_a0], dispatches next recursive
      /// call.
      struct _After_Node {
        tree *_s0;
        tree d_a2;
        unsigned int d_a1;
        tree d_a0;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        T1 _result;
        tree d_a2;
        unsigned int d_a1;
        tree d_a0;
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
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(
                _After_Node{d_a0.get(), *(d_a2), d_a1, *(d_a0)});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{_result, std::move(_f.d_a2),
                                            _f.d_a1, std::move(_f.d_a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = f0(_f.d_a0, _result, _f.d_a1, _f.d_a2, _f._result);
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, unsigned int &,
                                     tree &, T1 &>
    T1 tree_rect(T1 f, F1 &&f0) const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _After_Node: saves [_s0, d_a2, d_a1, d_a0], dispatches next recursive
      /// call.
      struct _After_Node {
        tree *_s0;
        tree d_a2;
        unsigned int d_a1;
        tree d_a0;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        T1 _result;
        tree d_a2;
        unsigned int d_a1;
        tree d_a0;
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
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(
                _After_Node{d_a0.get(), *(d_a2), d_a1, *(d_a0)});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{_result, std::move(_f.d_a2),
                                            _f.d_a1, std::move(_f.d_a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = f0(_f.d_a0, _result, _f.d_a1, _f.d_a2, _f._result);
        }
      }
      return _result;
    }
  };

  template <typename t_A> struct mylist {
    // TYPES
    struct Mynil {};

    struct Mycons {
      t_A d_a0;
      std::unique_ptr<mylist<t_A>> d_a1;
    };

    using variant_t = std::variant<Mynil, Mycons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    mylist() {}

    explicit mylist(Mynil _v) : d_v_(_v) {}

    explicit mylist(Mycons _v) : d_v_(std::move(_v)) {}

    mylist(const mylist<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    mylist(mylist<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    mylist<t_A> &operator=(const mylist<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    mylist<t_A> &operator=(mylist<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    mylist<t_A> clone() const {
      mylist<t_A> _out{};

      struct _CloneFrame {
        const mylist<t_A> *_src;
        mylist<t_A> *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const mylist<t_A> *_src = _frame._src;
        mylist<t_A> *_dst = _frame._dst;
        if (std::holds_alternative<Mynil>(_src->v())) {
          _dst->d_v_ = Mynil{};
        } else {
          const auto &_alt = std::get<Mycons>(_src->v());
          _dst->d_v_ = Mycons{
              _alt.d_a0, _alt.d_a1 ? std::make_unique<mylist<t_A>>() : nullptr};
          auto &_dst_alt = std::get<Mycons>(_dst->d_v_);
          if (_alt.d_a1) {
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    template <typename _U> explicit mylist(const mylist<_U> &_other) {
      if (std::holds_alternative<typename mylist<_U>::Mynil>(_other.v())) {
        this->d_v_ = Mynil{};
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename mylist<_U>::Mycons>(_other.v());
        this->d_v_ = Mycons{
            t_A(d_a0), d_a1 ? std::make_unique<mylist<t_A>>(*d_a1) : nullptr};
      }
    }

    static mylist<t_A> mynil() { return mylist(Mynil{}); }

    static mylist<t_A> mycons(t_A a0, mylist<t_A> a1) {
      return mylist(
          Mycons{std::move(a0), std::make_unique<mylist<t_A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~mylist() {
      std::vector<std::unique_ptr<mylist<t_A>>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](mylist<t_A> &_node) {
        if (std::holds_alternative<Mycons>(_node.d_v_)) {
          auto &_alt = std::get<Mycons>(_node.d_v_);
          if (_alt.d_a1) {
            _stack.push_back(std::move(_alt.d_a1));
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

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }

    mylist<t_A> myrev() const {
      return (*(this)).myrev_append(mylist<t_A>::mynil());
    }

    /// TEST 17: Build a list of closures, reverse it, and apply all.
    /// Probes whether closures survive list operations.
    mylist<t_A> myrev_append(mylist<t_A> acc) const {
      mylist<t_A> _result;
      const mylist *_loop_self = this;
      mylist<t_A> _loop_acc = std::move(acc);
      while (true) {
        auto &&_sv = *(_loop_self);
        if (std::holds_alternative<typename mylist<t_A>::Mynil>(_sv.v())) {
          _result = std::move(_loop_acc);
          break;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename mylist<t_A>::Mycons>(_sv.v());
          _loop_self = d_a1.get();
          _loop_acc = mylist<t_A>::mycons(d_a0, std::move(_loop_acc));
        }
      }
      return _result;
    }

    unsigned int mylength() const {
      const mylist *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const mylist *_self;
      };

      /// _Resume_Mycons: saves [_s0], resumes after recursive call with
      /// _result.
      struct _Resume_Mycons {
        decltype(1u) _s0;
      };

      using _Frame = std::variant<_Enter, _Resume_Mycons>;
      unsigned int _result{};
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
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename mylist<t_A>::Mynil>(_sv.v())) {
            _result = 0u;
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename mylist<t_A>::Mycons>(_sv.v());
            _stack.emplace_back(_Resume_Mycons{1u});
            _stack.emplace_back(_Enter{d_a1.get()});
          }
        } else {
          auto _f = std::move(std::get<_Resume_Mycons>(_frame));
          _result = (_f._s0 + _result);
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, t_A &, mylist<t_A> &, T1 &>
    T1 mylist_rec(T1 f, F1 &&f0) const {
      const mylist *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const mylist *_self;
      };

      /// _Resume_Mycons: saves [f0, d_a1, d_a0], resumes after recursive call
      /// with _result.
      struct _Resume_Mycons {
        F1 f0;
        mylist<t_A> d_a1;
        t_A d_a0;
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
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename mylist<t_A>::Mynil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename mylist<t_A>::Mycons>(_sv.v());
            _stack.emplace_back(_Resume_Mycons{f0, *(d_a1), d_a0});
            _stack.emplace_back(_Enter{d_a1.get()});
          }
        } else {
          auto _f = std::move(std::get<_Resume_Mycons>(_frame));
          _result = _f.f0(_f.d_a0, _f.d_a1, _result);
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, t_A &, mylist<t_A> &, T1 &>
    T1 mylist_rect(T1 f, F1 &&f0) const {
      const mylist *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const mylist *_self;
      };

      /// _Resume_Mycons: saves [f0, d_a1, d_a0], resumes after recursive call
      /// with _result.
      struct _Resume_Mycons {
        F1 f0;
        mylist<t_A> d_a1;
        t_A d_a0;
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
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename mylist<t_A>::Mynil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename mylist<t_A>::Mycons>(_sv.v());
            _stack.emplace_back(_Resume_Mycons{f0, *(d_a1), d_a0});
            _stack.emplace_back(_Enter{d_a1.get()});
          }
        } else {
          auto _f = std::move(std::get<_Resume_Mycons>(_frame));
          _result = _f.f0(_f.d_a0, _f.d_a1, _result);
        }
      }
      return _result;
    }
  };

  static inline const unsigned int test_dup_tree = []() {
    tree t = tree::node(tree::leaf(), 42u, tree::leaf());
    std::pair<tree, unsigned int> p = std::move(t).dup_tree();
    return (p.first.sum_values(0u) + p.second);
  }();
  static inline const unsigned int test_cps = []() {
    tree t = tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                        tree::node(tree::leaf(), 30u, tree::leaf()));
    return std::move(t).template with_tree<unsigned int>(
        [](const std::function<unsigned int(unsigned int)> f) {
          return (f(5u) + f(0u));
        });
  }();
  static inline const unsigned int test_compose = []() {
    tree t1 = tree::node(tree::leaf(), 10u, tree::leaf());
    tree t2 = tree::node(tree::leaf(), 20u, tree::leaf());
    return std::move(t1).compose_adders(std::move(t2), 5u);
  }();
  static inline const unsigned int test_partial_ctor = []() {
    return []() {
      tree t = tree::node(tree::leaf(), 42u, tree::leaf());
      std::function<tree(unsigned int, tree)> f = [&](unsigned int _x0,
                                                      tree _x1) -> tree {
        return std::move(t).make_node(_x0, _x1);
      };
      tree t2 = f(99u, tree::leaf());
      return std::move(t2).sum_values(0u);
    }();
  }();
  static inline const unsigned int test_double_wrap = []() {
    tree t = tree::node(tree::leaf(), 42u, tree::leaf());
    return std::move(t).double_wrap(10u);
  }();
  static inline const unsigned int test_tree_pair = []() {
    tree t = tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                        tree::node(tree::leaf(), 30u, tree::leaf()));
    std::pair<tree, tree> p = std::move(t).tree_pair();
    return (p.first.sum_values(0u) + p.second.sum_values(0u));
  }();
  /// TEST 7: Closure escaping through a list, then applied.
  static mylist<unsigned int>
  map_apply(const mylist<std::function<unsigned int(unsigned int)>> &fs,
            const unsigned int x);
  static unsigned int mysum(const mylist<unsigned int> &l);
  static inline const unsigned int test_closure_escape_list = []() {
    return []() {
      tree t1 = tree::node(tree::leaf(), 10u, tree::leaf());
      tree t2 = tree::node(tree::leaf(), 20u, tree::leaf());
      mylist<std::function<unsigned int(unsigned int)>> fs =
          mylist<std::function<unsigned int(unsigned int)>>::mycons(
              [=](unsigned int _x0) mutable -> unsigned int {
                return t1.sum_values(_x0);
              },
              mylist<std::function<unsigned int(unsigned int)>>::mycons(
                  [=](unsigned int _x0) mutable -> unsigned int {
                    return t2.sum_values(_x0);
                  },
                  mylist<std::function<unsigned int(unsigned int)>>::mynil()));
      return mysum(map_apply(std::move(fs), 5u));
    }();
  }();
  static inline const unsigned int test_extract_apply =
      tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                 tree::node(tree::leaf(), 30u, tree::leaf()))
          .extract_and_apply();
  static inline const unsigned int test_opt_closure = []() {
    tree t = tree::node(tree::leaf(), 42u, tree::leaf());
    auto _cs = t.opt_adder(true);
    if (_cs.has_value()) {
      const std::function<unsigned int(unsigned int)> &f = *_cs;
      return f(10u);
    } else {
      return 0u;
    }
  }();
  /// TEST 10: Two partial applications of the SAME function
  /// with DIFFERENT captured values. Both must independently own data.
  static inline const unsigned int test_two_partial = []() {
    return []() {
      tree t1 = tree::node(tree::leaf(), 10u, tree::leaf());
      tree t2 = tree::node(tree::leaf(), 20u, tree::leaf());
      std::function<unsigned int(unsigned int)> f =
          [&](unsigned int _x0) -> unsigned int {
        return std::move(t1).sum_values(_x0);
      };
      std::function<unsigned int(unsigned int)> g =
          [&](unsigned int _x0) -> unsigned int {
        return std::move(t2).sum_values(_x0);
      };
      return f(g(0u));
    }();
  }();
  static inline const unsigned int test_branch_true =
      tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                 tree::node(tree::leaf(), 30u, tree::leaf()))
          .branch_use(true);
  /// f 0 = 60
  static inline const unsigned int test_branch_false =
      tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                 tree::node(tree::leaf(), 30u, tree::leaf()))
          .branch_use(false);
  /// With t = Node Leaf 42 Leaf: 43 + 44 = 87
  static inline const unsigned int test_clone_close =
      tree::node(tree::leaf(), 42u, tree::leaf()).clone_and_close();
  /// TEST 13: Fold building tree from closures' results.
  static tree
  fold_tree_build(const mylist<std::function<unsigned int(unsigned int)>> &fs,
                  const unsigned int acc);
  static inline const unsigned int test_fold_tree = []() {
    return []() {
      tree t1 = tree::node(tree::leaf(), 10u, tree::leaf());
      tree t2 = tree::node(tree::leaf(), 20u, tree::leaf());
      mylist<std::function<unsigned int(unsigned int)>> fs =
          mylist<std::function<unsigned int(unsigned int)>>::mycons(
              [=](unsigned int _x0) mutable -> unsigned int {
                return t1.sum_values(_x0);
              },
              mylist<std::function<unsigned int(unsigned int)>>::mycons(
                  [=](unsigned int _x0) mutable -> unsigned int {
                    return t2.sum_values(_x0);
                  },
                  mylist<std::function<unsigned int(unsigned int)>>::mynil()));
      tree result = fold_tree_build(std::move(fs), 5u);
      return std::move(result).sum_values(0u);
    }();
  }();
  static inline const unsigned int test_pair_closure_tree = []() {
    tree t = tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                        tree::node(tree::leaf(), 30u, tree::leaf()));
    std::pair<std::function<unsigned int(unsigned int)>, tree> p =
        std::move(t).pair_closure_tree();
    return (p.first(5u) + p.second.sum_values(0u));
  }();
  static inline const unsigned int test_chain =
      tree::node(tree::leaf(), 10u, tree::leaf())
          .apply_chain(tree::node(tree::leaf(), 20u, tree::leaf()),
                       tree::node(tree::leaf(), 30u, tree::leaf()), 5u);
  static inline const unsigned int test_capture_branch =
      tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                 tree::node(tree::leaf(), 30u, tree::leaf()))
          .capture_in_branch(tree::leaf());
  static unsigned int
  apply_all(const mylist<std::function<unsigned int(unsigned int)>> &fs,
            const unsigned int x);
  static inline const unsigned int test_rev_closures = []() {
    return []() {
      tree t1 = tree::node(tree::leaf(), 10u, tree::leaf());
      tree t2 = tree::node(tree::leaf(), 20u, tree::leaf());
      tree t3 = tree::node(tree::leaf(), 30u, tree::leaf());
      mylist<std::function<unsigned int(unsigned int)>> fs =
          mylist<std::function<unsigned int(unsigned int)>>::mycons(
              [=](unsigned int _x0) mutable -> unsigned int {
                return t1.sum_values(_x0);
              },
              mylist<std::function<unsigned int(unsigned int)>>::mycons(
                  [=](unsigned int _x0) mutable -> unsigned int {
                    return t2.sum_values(_x0);
                  },
                  mylist<std::function<unsigned int(unsigned int)>>::mycons(
                      [=](unsigned int _x0) mutable -> unsigned int {
                        return t3.sum_values(_x0);
                      },
                      mylist<std::function<unsigned int(unsigned int)>>::
                          mynil())));
      mylist<std::function<unsigned int(unsigned int)>> rfs =
          std::move(fs).myrev();
      return apply_all(std::move(rfs), 5u);
    }();
  }();
  static inline const unsigned int test_build_from_partial = []() {
    tree t = tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                        tree::node(tree::leaf(), 30u, tree::leaf()));
    tree t2 = std::move(t).build_from_partial();
    return std::move(t2).sum_values(0u);
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE2
