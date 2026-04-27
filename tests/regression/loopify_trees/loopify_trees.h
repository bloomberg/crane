#ifndef INCLUDED_LOOPIFY_TREES
#define INCLUDED_LOOPIFY_TREES

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{
          d_a0, d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) List<t_A> app(List<t_A> m) const {
    std::unique_ptr<List<t_A>> _head{};
    std::unique_ptr<List<t_A>> *_write = &_head;
    const List *_loop_self = this;
    while (true) {
      auto &&_sv = *(_loop_self);
      if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
        *(_write) = std::make_unique<List<t_A>>(m);
        break;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
        auto _cell = std::make_unique<List<t_A>>(
            typename List<t_A>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write = &std::get<typename List<t_A>::Cons>((*_write)->v_mut()).d_a1;
        _loop_self = d_a1.get();
        continue;
      }
    }
    return std::move(*(_head));
  }
};

/// Consolidated UNIQUE tree algorithms - domain-specific tree operations.
struct LoopifyTrees {
  template <typename t_A> struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::unique_ptr<tree<t_A>> d_a0;
      t_A d_a1;
      std::unique_ptr<tree<t_A>> d_a2;
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

    tree(const tree<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    tree(tree<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    tree<t_A> &operator=(const tree<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    tree<t_A> &operator=(tree<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) tree<t_A> clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Leaf>(_sv.v())) {
        return tree<t_A>(Leaf{});
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<Node>(_sv.v());
        return tree<t_A>(
            Node{d_a0 ? std::make_unique<LoopifyTrees::tree<t_A>>(d_a0->clone())
                      : nullptr,
                 d_a1,
                 d_a2 ? std::make_unique<LoopifyTrees::tree<t_A>>(d_a2->clone())
                      : nullptr});
      }
    }

    // CREATORS
    template <typename _U> explicit tree(const tree<_U> &_other) {
      if (std::holds_alternative<typename tree<_U>::Leaf>(_other.v())) {
        d_v_ = Leaf{};
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename tree<_U>::Node>(_other.v());
        d_v_ =
            Node{d_a0 ? std::make_unique<tree<t_A>>(*d_a0) : nullptr, t_A(d_a1),
                 d_a2 ? std::make_unique<tree<t_A>>(*d_a2) : nullptr};
      }
    }

    __attribute__((pure)) static tree<t_A> leaf() { return tree(Leaf{}); }

    __attribute__((pure)) static tree<t_A> node(const tree<t_A> &a0, t_A a1,
                                                const tree<t_A> &a2) {
      return tree(Node{std::make_unique<tree<t_A>>(a0), std::move(a1),
                       std::make_unique<tree<t_A>>(a2)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    /// tree_map f t applies f to all values in tree.
    template <typename T1, MapsTo<T1, t_A> F0>
    __attribute__((pure)) tree<T1> tree_map(F0 &&f) const {
      const tree *_self = this;

      struct _Enter {
        const tree *_self;
      };

      struct _Call1 {
        tree<t_A> *_s0;
        decltype(std::declval<F0 &>()(std::declval<t_A &>())) _s1;
      };

      struct _Call2 {
        tree<T1> _s0;
        decltype(std::declval<F0 &>()(std::declval<t_A &>())) _s1;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      tree<T1> _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename tree<t_A>::Leaf>(_sv.v())) {
            _result = tree<T1>::leaf();
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename tree<t_A>::Node>(_sv.v());
            _stack.emplace_back(_Call1{d_a0.get(), f(d_a1)});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result, _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = tree<T1>::node(_result, _f._s1, _f._s0);
        }
      }
      return _result;
    }

    /// mirror_equal t1 t2 checks if t1 and t2 are mirror images.
    __attribute__((pure)) bool mirror_equal(const tree<t_A> &t2) const {
      const tree *_self = this;

      struct _Enter {
        const tree *_self;
        const tree<t_A> t2;
      };

      struct _Call1 {
        tree<t_A> *_s0;
        tree<t_A> _s1;
        decltype(true) _s2;
      };

      struct _Call2 {
        bool _s0;
        decltype(true) _s1;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      bool _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self, t2});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          const tree<t_A> t2 = _f.t2;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename tree<t_A>::Leaf>(_sv.v())) {
            if (std::holds_alternative<typename tree<t_A>::Leaf>(t2.v())) {
              _result = true;
            } else {
              _result = false;
            }
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename tree<t_A>::Node>(_sv.v());
            if (std::holds_alternative<typename tree<t_A>::Leaf>(t2.v())) {
              _result = false;
            } else {
              const auto &[d_a00, d_a10, d_a20] =
                  std::get<typename tree<t_A>::Node>(t2.v());
              _stack.emplace_back(_Call1{d_a0.get(), *(d_a20), true});
              _stack.emplace_back(_Enter{d_a2.get(), *(d_a00)});
            }
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result, _f._s2});
          _stack.emplace_back(_Enter{_f._s0, _f._s1});
        } else {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = ((_result && _f._s0) && _f._s1);
        }
      }
      return _result;
    }

    /// tree_to_list inorder traversal.
    __attribute__((pure)) List<t_A> tree_to_list() const {
      const tree *_self = this;

      struct _Enter {
        const tree *_self;
      };

      struct _Call1 {
        tree<t_A> *_s0;
        t_A _s1;
      };

      struct _Call2 {
        List<t_A> _s0;
        t_A _s1;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      List<t_A> _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename tree<t_A>::Leaf>(_sv.v())) {
            _result = List<t_A>::nil();
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename tree<t_A>::Node>(_sv.v());
            _stack.emplace_back(_Call1{d_a0.get(), d_a1});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result, _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = _result.app(List<t_A>::cons(_f._s1, _f._s0));
        }
      }
      return _result;
    }

    /// count_leaves counts leaf nodes.
    __attribute__((pure)) unsigned int count_leaves() const {
      const tree *_self = this;

      struct _Enter {
        const tree *_self;
      };

      struct _Call1 {
        tree<t_A> *_s0;
      };

      struct _Call2 {
        unsigned int _s0;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename tree<t_A>::Leaf>(_sv.v())) {
            _result = 1u;
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename tree<t_A>::Node>(_sv.v());
            _stack.emplace_back(_Call1{d_a0.get()});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = (_result + _f._s0);
        }
      }
      return _result;
    }

    t_A rightmost(const t_A default0) const {
      t_A _result;
      const tree *_loop_self = this;
      while (true) {
        auto &&_sv = *(_loop_self);
        if (std::holds_alternative<typename tree<t_A>::Leaf>(_sv.v())) {
          _result = default0;
          break;
        } else {
          const auto &[d_a0, d_a1, d_a2] =
              std::get<typename tree<t_A>::Node>(_sv.v());
          auto &&_sv = *(d_a2);
          if (std::holds_alternative<typename tree<t_A>::Leaf>(_sv.v())) {
            _result = d_a1;
            break;
          } else {
            _loop_self = d_a2.get();
          }
        }
      }
      return _result;
    }

    /// leftmost/rightmost finds edge values.
    t_A leftmost(const t_A default0) const {
      t_A _result;
      const tree *_loop_self = this;
      while (true) {
        auto &&_sv = *(_loop_self);
        if (std::holds_alternative<typename tree<t_A>::Leaf>(_sv.v())) {
          _result = default0;
          break;
        } else {
          const auto &[d_a0, d_a1, d_a2] =
              std::get<typename tree<t_A>::Node>(_sv.v());
          auto &&_sv = *(d_a0);
          if (std::holds_alternative<typename tree<t_A>::Leaf>(_sv.v())) {
            _result = d_a1;
            break;
          } else {
            _loop_self = d_a0.get();
          }
        }
      }
      return _result;
    }

    /// same_shape tests structural equality.
    template <typename T1>
    __attribute__((pure)) bool same_shape(const tree<T1> &t2) const {
      const tree *_self = this;
      auto &&_sv = *(_self);
      if (std::holds_alternative<typename tree<t_A>::Leaf>(_sv.v())) {
        if (std::holds_alternative<typename tree<T1>::Leaf>(t2.v())) {
          return true;
        } else {
          return false;
        }
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename tree<t_A>::Node>(_sv.v());
        if (std::holds_alternative<typename tree<T1>::Leaf>(t2.v())) {
          return false;
        } else {
          const auto &[d_a00, d_a10, d_a20] =
              std::get<typename tree<T1>::Node>(t2.v());
          if ((*(d_a0)).template same_shape<T1>(*(d_a00))) {
            return (*(d_a2)).template same_shape<T1>(*(d_a20));
          } else {
            return false;
          }
        }
      }
    }

    __attribute__((pure)) tree<t_A> mirror() const {
      const tree *_self = this;

      struct _Enter {
        const tree *_self;
      };

      struct _Call1 {
        tree<t_A> *_s0;
        t_A _s1;
      };

      struct _Call2 {
        tree<t_A> _s0;
        t_A _s1;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      tree<t_A> _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename tree<t_A>::Leaf>(_sv.v())) {
            _result = tree<t_A>::leaf();
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename tree<t_A>::Node>(_sv.v());
            _stack.emplace_back(_Call1{d_a2.get(), d_a1});
            _stack.emplace_back(_Enter{d_a0.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result, _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = tree<t_A>::node(_result, _f._s1, _f._s0);
        }
      }
      return _result;
    }

    __attribute__((pure)) unsigned int tree_size() const {
      const tree *_self = this;

      struct _Enter {
        const tree *_self;
      };

      struct _Call1 {
        tree<t_A> *_s0;
      };

      struct _Call2 {
        unsigned int _s0;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename tree<t_A>::Leaf>(_sv.v())) {
            _result = 0u;
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename tree<t_A>::Node>(_sv.v());
            _stack.emplace_back(_Call1{d_a0.get()});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = ((_result + _f._s0) + 1);
        }
      }
      return _result;
    }

    __attribute__((pure)) unsigned int tree_height() const {
      const tree *_self = this;
      auto &&_sv = *(_self);
      if (std::holds_alternative<typename tree<t_A>::Leaf>(_sv.v())) {
        return 0u;
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename tree<t_A>::Node>(_sv.v());
        unsigned int lh = (*(d_a0)).tree_height();
        unsigned int rh = (*(d_a2)).tree_height();
        return ([&]() -> unsigned int {
          if (lh <= rh) {
            return rh;
          } else {
            return lh;
          }
        }() + 1);
      }
    }

    template <typename T1, MapsTo<T1, tree<t_A>, T1, t_A, tree<t_A>, T1> F1>
    T1 tree_rec(const T1 f, F1 &&f0) const {
      const tree *_self = this;

      struct _Enter {
        const tree *_self;
      };

      struct _Call1 {
        tree<t_A> *_s0;
        tree<t_A> _s1;
        t_A _s2;
        tree<t_A> _s3;
      };

      struct _Call2 {
        T1 _s0;
        tree<t_A> _s1;
        t_A _s2;
        tree<t_A> _s3;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename tree<t_A>::Leaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename tree<t_A>::Node>(_sv.v());
            _stack.emplace_back(_Call1{d_a0.get(), *(d_a2), d_a1, *(d_a0)});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2, _f._s3});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = f0(_f._s3, _result, _f._s2, _f._s1, _f._s0);
        }
      }
      return _result;
    }

    template <typename T1, MapsTo<T1, tree<t_A>, T1, t_A, tree<t_A>, T1> F1>
    T1 tree_rect(const T1 f, F1 &&f0) const {
      const tree *_self = this;

      struct _Enter {
        const tree *_self;
      };

      struct _Call1 {
        tree<t_A> *_s0;
        tree<t_A> _s1;
        t_A _s2;
        tree<t_A> _s3;
      };

      struct _Call2 {
        T1 _s0;
        tree<t_A> _s1;
        t_A _s2;
        tree<t_A> _s3;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename tree<t_A>::Leaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename tree<t_A>::Node>(_sv.v());
            _stack.emplace_back(_Call1{d_a0.get(), *(d_a2), d_a1, *(d_a0)});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2, _f._s3});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = f0(_f._s3, _result, _f._s2, _f._s1, _f._s0);
        }
      }
      return _result;
    }
  };

  __attribute__((pure)) static unsigned int
  tree_sum(const tree<unsigned int> &t);
  /// leaf_sum sums only leaf values.
  __attribute__((pure)) static unsigned int
  leaf_sum(const tree<unsigned int> &t);
  /// insert_bst BST insertion.
  __attribute__((pure)) static tree<unsigned int>
  insert_bst(unsigned int x, const tree<unsigned int> &t);
  /// count_paths t n counts root-to-leaf paths that sum to n.
  __attribute__((pure)) static unsigned int
  count_paths(const tree<unsigned int> &t, const unsigned int &n);
  /// sum_of_max_branches sums maximum values along each path.
  __attribute__((pure)) static unsigned int
  sum_of_max_branches(const tree<unsigned int> &t);

  struct ternary {
    // TYPES
    struct TLeaf {};

    struct TNode {
      std::unique_ptr<ternary> d_a0;
      std::unique_ptr<ternary> d_a1;
      std::unique_ptr<ternary> d_a2;
      unsigned int d_a3;
    };

    using variant_t = std::variant<TLeaf, TNode>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    ternary() {}

    explicit ternary(TLeaf _v) : d_v_(_v) {}

    explicit ternary(TNode _v) : d_v_(std::move(_v)) {}

    ternary(const ternary &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    ternary(ternary &&_other) : d_v_(std::move(_other.d_v_)) {}

    ternary &operator=(const ternary &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    ternary &operator=(ternary &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) ternary clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<TLeaf>(_sv.v())) {
        return ternary(TLeaf{});
      } else {
        const auto &[d_a0, d_a1, d_a2, d_a3] = std::get<TNode>(_sv.v());
        return ternary(
            TNode{d_a0 ? std::make_unique<LoopifyTrees::ternary>(d_a0->clone())
                       : nullptr,
                  d_a1 ? std::make_unique<LoopifyTrees::ternary>(d_a1->clone())
                       : nullptr,
                  d_a2 ? std::make_unique<LoopifyTrees::ternary>(d_a2->clone())
                       : nullptr,
                  d_a3});
      }
    }

    // CREATORS
    __attribute__((pure)) static ternary tleaf() { return ternary(TLeaf{}); }

    __attribute__((pure)) static ternary tnode(const ternary &a0,
                                               const ternary &a1,
                                               const ternary &a2,
                                               unsigned int a3) {
      return ternary(TNode{std::make_unique<ternary>(a0),
                           std::make_unique<ternary>(a1),
                           std::make_unique<ternary>(a2), std::move(a3)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int ternary_depth() const {
      const ternary *_self = this;
      auto &&_sv = *(_self);
      if (std::holds_alternative<typename ternary::TLeaf>(_sv.v())) {
        return 0u;
      } else {
        const auto &[d_a0, d_a1, d_a2, d_a3] =
            std::get<typename ternary::TNode>(_sv.v());
        unsigned int d1 = (*(d_a0)).ternary_depth();
        unsigned int d2 = (*(d_a1)).ternary_depth();
        unsigned int d3 = (*(d_a2)).ternary_depth();
        return ([&]() -> unsigned int {
          if ([&]() -> unsigned int {
                if (d1 <= d2) {
                  return d2;
                } else {
                  return d1;
                }
              }() <= d3) {
            return d3;
          } else {
            if (d1 <= d2) {
              return d2;
            } else {
              return d1;
            }
          }
        }() + 1);
      }
    }

    __attribute__((pure)) unsigned int ternary_sum() const {
      const ternary *_self = this;

      struct _Enter {
        const ternary *_self;
      };

      struct _Call1 {
        const ternary *_s0;
        const ternary *_s1;
        unsigned int _s2;
      };

      struct _Call2 {
        unsigned int _s0;
        const ternary *_s1;
        unsigned int _s2;
      };

      struct _Call3 {
        unsigned int _s0;
        unsigned int _s1;
        unsigned int _s2;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const ternary *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename ternary::TLeaf>(_sv.v())) {
            _result = 0u;
          } else {
            const auto &[d_a0, d_a1, d_a2, d_a3] =
                std::get<typename ternary::TNode>(_sv.v());
            _stack.emplace_back(_Call1{d_a1.get(), d_a0.get(), d_a3});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _stack.emplace_back(_Call3{_f._s0, _result, _f._s2});
          _stack.emplace_back(_Enter{_f._s1});
        } else {
          auto _f = std::move(std::get<_Call3>(_frame));
          _result = (_f._s2 + (_result + (_f._s1 + _f._s0)));
        }
      }
      return _result;
    }

    template <
        typename T1,
        MapsTo<T1, ternary, T1, ternary, T1, ternary, T1, unsigned int> F1>
    T1 ternary_rec(const T1 f, F1 &&f0) const {
      const ternary *_self = this;

      struct _Enter {
        const ternary *_self;
      };

      struct _Call1 {
        const ternary *_s0;
        const ternary *_s1;
        unsigned int _s2;
        ternary _s3;
        ternary _s4;
        ternary _s5;
      };

      struct _Call2 {
        T1 _s0;
        const ternary *_s1;
        unsigned int _s2;
        ternary _s3;
        ternary _s4;
        ternary _s5;
      };

      struct _Call3 {
        T1 _s0;
        T1 _s1;
        unsigned int _s2;
        ternary _s3;
        ternary _s4;
        ternary _s5;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const ternary *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename ternary::TLeaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[d_a0, d_a1, d_a2, d_a3] =
                std::get<typename ternary::TNode>(_sv.v());
            _stack.emplace_back(_Call1{d_a1.get(), d_a0.get(), d_a3, *(d_a2),
                                       *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(
              _Call2{_result, _f._s1, _f._s2, _f._s3, _f._s4, _f._s5});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _stack.emplace_back(
              _Call3{_f._s0, _result, _f._s2, _f._s3, _f._s4, _f._s5});
          _stack.emplace_back(_Enter{_f._s1});
        } else {
          auto _f = std::move(std::get<_Call3>(_frame));
          _result = f0(_f._s5, _result, _f._s4, _f._s1, _f._s3, _f._s0, _f._s2);
        }
      }
      return _result;
    }

    template <
        typename T1,
        MapsTo<T1, ternary, T1, ternary, T1, ternary, T1, unsigned int> F1>
    T1 ternary_rect(const T1 f, F1 &&f0) const {
      const ternary *_self = this;

      struct _Enter {
        const ternary *_self;
      };

      struct _Call1 {
        const ternary *_s0;
        const ternary *_s1;
        unsigned int _s2;
        ternary _s3;
        ternary _s4;
        ternary _s5;
      };

      struct _Call2 {
        T1 _s0;
        const ternary *_s1;
        unsigned int _s2;
        ternary _s3;
        ternary _s4;
        ternary _s5;
      };

      struct _Call3 {
        T1 _s0;
        T1 _s1;
        unsigned int _s2;
        ternary _s3;
        ternary _s4;
        ternary _s5;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const ternary *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename ternary::TLeaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[d_a0, d_a1, d_a2, d_a3] =
                std::get<typename ternary::TNode>(_sv.v());
            _stack.emplace_back(_Call1{d_a1.get(), d_a0.get(), d_a3, *(d_a2),
                                       *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(
              _Call2{_result, _f._s1, _f._s2, _f._s3, _f._s4, _f._s5});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _stack.emplace_back(
              _Call3{_f._s0, _result, _f._s2, _f._s3, _f._s4, _f._s5});
          _stack.emplace_back(_Enter{_f._s1});
        } else {
          auto _f = std::move(std::get<_Call3>(_frame));
          _result = f0(_f._s5, _result, _f._s4, _f._s1, _f._s3, _f._s0, _f._s2);
        }
      }
      return _result;
    }
  };

  /// Rose tree: a tree with variable number of children.
  struct rose {
    // TYPES
    struct RNode {
      unsigned int d_a0;
      std::unique_ptr<List<rose>> d_a1;
    };

    using variant_t = std::variant<RNode>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    rose() {}

    explicit rose(RNode _v) : d_v_(std::move(_v)) {}

    rose(const rose &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    rose(rose &&_other) : d_v_(std::move(_other.d_v_)) {}

    rose &operator=(const rose &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    rose &operator=(rose &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) rose clone() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<RNode>(_sv.v());
      return rose(RNode{
          d_a0, d_a1 ? std::make_unique<List<LoopifyTrees::rose>>(d_a1->clone())
                     : nullptr});
    }

    // CREATORS
    __attribute__((pure)) static rose rnode(unsigned int a0,
                                            const List<rose> &a1) {
      return rose(RNode{std::move(a0), std::make_unique<List<rose>>(a1)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    /// rose_depth t computes the depth of a rose tree.
    __attribute__((pure)) unsigned int rose_depth() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<typename rose::RNode>(_sv.v());
      return (depth_rose_list_fuel(1000u, *(d_a1)) + 1);
    }

    /// rose_flatten t flattens a rose tree to a list (pre-order).
    __attribute__((pure)) List<unsigned int> rose_flatten() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<typename rose::RNode>(_sv.v());
      return List<unsigned int>::cons(d_a0,
                                      flatten_rose_list_fuel(1000u, *(d_a1)));
    }

    /// rose_map f t applies f to all values in a rose tree.
    template <MapsTo<unsigned int, unsigned int> F0>
    __attribute__((pure)) rose rose_map(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<typename rose::RNode>(_sv.v());
      return rose::rnode(f(d_a0), map_rose_list_fuel(1000u, f, *(d_a1)));
    }

    /// rose_sum t sums all values in a rose tree.
    __attribute__((pure)) unsigned int rose_sum() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<typename rose::RNode>(_sv.v());
      return (d_a0 + sum_rose_list_fuel(1000u, *(d_a1)));
    }

    template <typename T1, MapsTo<T1, unsigned int, List<rose>> F0>
    T1 rose_rec(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<typename rose::RNode>(_sv.v());
      return f(d_a0, *(d_a1));
    }

    template <typename T1, MapsTo<T1, unsigned int, List<rose>> F0>
    T1 rose_rect(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<typename rose::RNode>(_sv.v());
      return f(d_a0, *(d_a1));
    }
  };

  /// Helper: sum all values in a list of rose trees (processes both tree and
  /// list levels in one recursive function to enable full loopification).
  __attribute__((pure)) static unsigned int
  sum_rose_list_fuel(const unsigned int &fuel, const List<rose> &cs);

  /// Helper: map function over all values in a list of rose trees.
  template <MapsTo<unsigned int, unsigned int> F1>
  __attribute__((pure)) static List<rose>
  map_rose_list_fuel(const unsigned int &fuel, F1 &&f, const List<rose> &cs) {
    if (fuel <= 0) {
      return List<rose>::nil();
    } else {
      unsigned int g = fuel - 1;
      if (std::holds_alternative<typename List<rose>::Nil>(cs.v())) {
        return List<rose>::nil();
      } else {
        const auto &[d_a0, d_a1] = std::get<typename List<rose>::Cons>(cs.v());
        const auto &[d_a00, d_a10] = std::get<typename rose::RNode>(d_a0.v());
        return List<rose>::cons(
            rose::rnode(f(d_a00), map_rose_list_fuel(g, f, *(d_a10))),
            map_rose_list_fuel(g, f, *(d_a1)));
      }
    }
  }

  /// Helper: flatten a list of rose trees to a flat list of nats.
  __attribute__((pure)) static List<unsigned int>
  flatten_rose_list_fuel(const unsigned int &fuel, const List<rose> &cs);
  /// Helper: compute maximum depth among a list of rose trees.
  __attribute__((pure)) static unsigned int
  depth_rose_list_fuel(const unsigned int &fuel, const List<rose> &cs);
  /// tree_max t1 t2 element-wise maximum of two trees.
  __attribute__((pure)) static tree<unsigned int>
  tree_max(tree<unsigned int> t1, tree<unsigned int> t2);
  /// Helper: extract values from trees.
  __attribute__((pure)) static List<unsigned int>
  extract_tree_values(const List<tree<unsigned int>> &ts);
  /// Helper: extract children from trees.
  __attribute__((pure)) static List<tree<unsigned int>>
  extract_tree_children(const List<tree<unsigned int>> &ts);
  /// tree_levels t returns list of lists, one per level (breadth-first).
  __attribute__((pure)) static List<List<unsigned int>>
  tree_levels_fuel(const unsigned int &fuel,
                   const List<tree<unsigned int>> &trees);
  __attribute__((pure)) static List<List<unsigned int>>
  tree_levels(tree<unsigned int> t);
  /// count_nodes t returns tuple (node_count, sum_of_values).
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  count_nodes(const tree<unsigned int> &t);
  /// Helper: append two lists of lists.
  __attribute__((pure)) static List<List<unsigned int>>
  append_list_lists(const List<List<unsigned int>> &l1,
                    List<List<unsigned int>> l2);
  /// Helper: prepend value to all lists in a list of lists.
  __attribute__((pure)) static List<List<unsigned int>>
  map_cons_to_all(unsigned int x, const List<List<unsigned int>> &lsts);
  /// paths t returns all root-to-leaf paths in tree.
  __attribute__((pure)) static List<List<unsigned int>>
  paths(const tree<unsigned int> &t);
  /// collect_sorted t collects and sorts all tree values.
  __attribute__((pure)) static List<unsigned int>
  collect_unsorted(const tree<unsigned int> &t);
  /// Simple insertion sort for collect_sorted.
  __attribute__((pure)) static List<unsigned int>
  insert_sorted(unsigned int x, const List<unsigned int> &l);
  __attribute__((pure)) static List<unsigned int>
  sort_list(const List<unsigned int> &l);
  __attribute__((pure)) static List<unsigned int> collect_sorted(
      const tree<unsigned int>
          &t); /// or_search p t searches tree for element satisfying predicate.

  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static bool or_search(F0 &&p,
                                              const tree<unsigned int> &t) {
    if (std::holds_alternative<typename tree<unsigned int>::Leaf>(t.v())) {
      return false;
    } else {
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename tree<unsigned int>::Node>(t.v());
      if (p(d_a1)) {
        return true;
      } else {
        return (or_search(p, *(d_a0)) || or_search(p, *(d_a2)));
      }
    }
  }

  struct quadtree {
    // TYPES
    struct QLeaf {
      unsigned int d_a0;
    };

    struct Quad {
      std::unique_ptr<quadtree> d_a0;
      std::unique_ptr<quadtree> d_a1;
      std::unique_ptr<quadtree> d_a2;
      std::unique_ptr<quadtree> d_a3;
    };

    using variant_t = std::variant<QLeaf, Quad>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    quadtree() {}

    explicit quadtree(QLeaf _v) : d_v_(std::move(_v)) {}

    explicit quadtree(Quad _v) : d_v_(std::move(_v)) {}

    quadtree(const quadtree &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    quadtree(quadtree &&_other) : d_v_(std::move(_other.d_v_)) {}

    quadtree &operator=(const quadtree &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    quadtree &operator=(quadtree &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) quadtree clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<QLeaf>(_sv.v())) {
        const auto &[d_a0] = std::get<QLeaf>(_sv.v());
        return quadtree(QLeaf{d_a0});
      } else {
        const auto &[d_a0, d_a1, d_a2, d_a3] = std::get<Quad>(_sv.v());
        return quadtree(
            Quad{d_a0 ? std::make_unique<LoopifyTrees::quadtree>(d_a0->clone())
                      : nullptr,
                 d_a1 ? std::make_unique<LoopifyTrees::quadtree>(d_a1->clone())
                      : nullptr,
                 d_a2 ? std::make_unique<LoopifyTrees::quadtree>(d_a2->clone())
                      : nullptr,
                 d_a3 ? std::make_unique<LoopifyTrees::quadtree>(d_a3->clone())
                      : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static quadtree qleaf(unsigned int a0) {
      return quadtree(QLeaf{std::move(a0)});
    }

    __attribute__((pure)) static quadtree quad(const quadtree &a0,
                                               const quadtree &a1,
                                               const quadtree &a2,
                                               const quadtree &a3) {
      return quadtree(
          Quad{std::make_unique<quadtree>(a0), std::make_unique<quadtree>(a1),
               std::make_unique<quadtree>(a2), std::make_unique<quadtree>(a3)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    /// quad_depth t computes depth of quadtree.
    __attribute__((pure)) unsigned int quad_depth() const {
      const quadtree *_self = this;

      struct _Enter {
        const quadtree *_self;
      };

      struct _Call1 {
        const quadtree *_s0;
        const quadtree *_s1;
        const quadtree *_s2;
      };

      struct _Call2 {
        unsigned int _s0;
        const quadtree *_s1;
        const quadtree *_s2;
      };

      struct _Call3 {
        unsigned int _s0;
        unsigned int _s1;
        const quadtree *_s2;
      };

      struct _Call4 {
        unsigned int _s0;
        unsigned int _s1;
        unsigned int _s2;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const quadtree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
            _result = 0u;
          } else {
            const auto &[d_a0, d_a1, d_a2, d_a3] =
                std::get<typename quadtree::Quad>(_sv.v());
            _stack.emplace_back(_Call1{d_a2.get(), d_a1.get(), d_a0.get()});
            _stack.emplace_back(_Enter{d_a3.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _stack.emplace_back(_Call3{_f._s0, _result, _f._s2});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_Call3>(_frame)) {
          auto _f = std::move(std::get<_Call3>(_frame));
          _stack.emplace_back(_Call4{_f._s0, _f._s1, _result});
          _stack.emplace_back(_Enter{_f._s2});
        } else {
          auto _f = std::move(std::get<_Call4>(_frame));
          _result = (max4_impl(_result, _f._s2, _f._s1, _f._s0) + 1);
        }
      }
      return _result;
    }

    /// quad_sum t sums all values in a quadtree.
    __attribute__((pure)) unsigned int quad_sum() const {
      const quadtree *_self = this;

      struct _Enter {
        const quadtree *_self;
      };

      struct _Call1 {
        const quadtree *_s0;
        const quadtree *_s1;
        const quadtree *_s2;
      };

      struct _Call2 {
        unsigned int _s0;
        const quadtree *_s1;
        const quadtree *_s2;
      };

      struct _Call3 {
        unsigned int _s0;
        unsigned int _s1;
        const quadtree *_s2;
      };

      struct _Call4 {
        unsigned int _s0;
        unsigned int _s1;
        unsigned int _s2;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const quadtree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
            const auto &[d_a0] = std::get<typename quadtree::QLeaf>(_sv.v());
            _result = d_a0;
          } else {
            const auto &[d_a0, d_a1, d_a2, d_a3] =
                std::get<typename quadtree::Quad>(_sv.v());
            _stack.emplace_back(_Call1{d_a2.get(), d_a1.get(), d_a0.get()});
            _stack.emplace_back(_Enter{d_a3.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _stack.emplace_back(_Call3{_f._s0, _result, _f._s2});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_Call3>(_frame)) {
          auto _f = std::move(std::get<_Call3>(_frame));
          _stack.emplace_back(_Call4{_f._s0, _f._s1, _result});
          _stack.emplace_back(_Enter{_f._s2});
        } else {
          auto _f = std::move(std::get<_Call4>(_frame));
          _result = (_result + (_f._s2 + (_f._s1 + _f._s0)));
        }
      }
      return _result;
    }

    template <
        typename T1, MapsTo<T1, unsigned int> F0,
        MapsTo<T1, quadtree, T1, quadtree, T1, quadtree, T1, quadtree, T1> F1>
    T1 quadtree_rec(F0 &&f, F1 &&f0) const {
      const quadtree *_self = this;

      struct _Enter {
        const quadtree *_self;
      };

      struct _Call1 {
        const quadtree *_s0;
        const quadtree *_s1;
        const quadtree *_s2;
        quadtree _s3;
        quadtree _s4;
        quadtree _s5;
        quadtree _s6;
      };

      struct _Call2 {
        T1 _s0;
        const quadtree *_s1;
        const quadtree *_s2;
        quadtree _s3;
        quadtree _s4;
        quadtree _s5;
        quadtree _s6;
      };

      struct _Call3 {
        T1 _s0;
        T1 _s1;
        const quadtree *_s2;
        quadtree _s3;
        quadtree _s4;
        quadtree _s5;
        quadtree _s6;
      };

      struct _Call4 {
        T1 _s0;
        T1 _s1;
        T1 _s2;
        quadtree _s3;
        quadtree _s4;
        quadtree _s5;
        quadtree _s6;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const quadtree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
            const auto &[d_a0] = std::get<typename quadtree::QLeaf>(_sv.v());
            _result = f(d_a0);
          } else {
            const auto &[d_a0, d_a1, d_a2, d_a3] =
                std::get<typename quadtree::Quad>(_sv.v());
            _stack.emplace_back(_Call1{d_a2.get(), d_a1.get(), d_a0.get(),
                                       *(d_a3), *(d_a2), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a3.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(
              _Call2{_result, _f._s1, _f._s2, _f._s3, _f._s4, _f._s5, _f._s6});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _stack.emplace_back(
              _Call3{_f._s0, _result, _f._s2, _f._s3, _f._s4, _f._s5, _f._s6});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_Call3>(_frame)) {
          auto _f = std::move(std::get<_Call3>(_frame));
          _stack.emplace_back(
              _Call4{_f._s0, _f._s1, _result, _f._s3, _f._s4, _f._s5, _f._s6});
          _stack.emplace_back(_Enter{_f._s2});
        } else {
          auto _f = std::move(std::get<_Call4>(_frame));
          _result = f0(_f._s6, _result, _f._s5, _f._s2, _f._s4, _f._s1, _f._s3,
                       _f._s0);
        }
      }
      return _result;
    }

    template <
        typename T1, MapsTo<T1, unsigned int> F0,
        MapsTo<T1, quadtree, T1, quadtree, T1, quadtree, T1, quadtree, T1> F1>
    T1 quadtree_rect(F0 &&f, F1 &&f0) const {
      const quadtree *_self = this;

      struct _Enter {
        const quadtree *_self;
      };

      struct _Call1 {
        const quadtree *_s0;
        const quadtree *_s1;
        const quadtree *_s2;
        quadtree _s3;
        quadtree _s4;
        quadtree _s5;
        quadtree _s6;
      };

      struct _Call2 {
        T1 _s0;
        const quadtree *_s1;
        const quadtree *_s2;
        quadtree _s3;
        quadtree _s4;
        quadtree _s5;
        quadtree _s6;
      };

      struct _Call3 {
        T1 _s0;
        T1 _s1;
        const quadtree *_s2;
        quadtree _s3;
        quadtree _s4;
        quadtree _s5;
        quadtree _s6;
      };

      struct _Call4 {
        T1 _s0;
        T1 _s1;
        T1 _s2;
        quadtree _s3;
        quadtree _s4;
        quadtree _s5;
        quadtree _s6;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const quadtree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
            const auto &[d_a0] = std::get<typename quadtree::QLeaf>(_sv.v());
            _result = f(d_a0);
          } else {
            const auto &[d_a0, d_a1, d_a2, d_a3] =
                std::get<typename quadtree::Quad>(_sv.v());
            _stack.emplace_back(_Call1{d_a2.get(), d_a1.get(), d_a0.get(),
                                       *(d_a3), *(d_a2), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a3.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(
              _Call2{_result, _f._s1, _f._s2, _f._s3, _f._s4, _f._s5, _f._s6});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _stack.emplace_back(
              _Call3{_f._s0, _result, _f._s2, _f._s3, _f._s4, _f._s5, _f._s6});
          _stack.emplace_back(_Enter{_f._s1});
        } else if (std::holds_alternative<_Call3>(_frame)) {
          auto _f = std::move(std::get<_Call3>(_frame));
          _stack.emplace_back(
              _Call4{_f._s0, _f._s1, _result, _f._s3, _f._s4, _f._s5, _f._s6});
          _stack.emplace_back(_Enter{_f._s2});
        } else {
          auto _f = std::move(std::get<_Call4>(_frame));
          _result = f0(_f._s6, _result, _f._s5, _f._s2, _f._s4, _f._s1, _f._s3,
                       _f._s0);
        }
      }
      return _result;
    }
  };

  /// Helper: max of 4 values using nested max.
  __attribute__((pure)) static unsigned int
  max4_impl(unsigned int a, unsigned int b, unsigned int c, unsigned int d);

  /// Simple binary tree with values only at leaves.
  struct simple_tree {
    // TYPES
    struct SLeaf {
      unsigned int d_a0;
    };

    struct SNode {
      std::unique_ptr<simple_tree> d_a0;
      std::unique_ptr<simple_tree> d_a1;
    };

    using variant_t = std::variant<SLeaf, SNode>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    simple_tree() {}

    explicit simple_tree(SLeaf _v) : d_v_(std::move(_v)) {}

    explicit simple_tree(SNode _v) : d_v_(std::move(_v)) {}

    simple_tree(const simple_tree &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    simple_tree(simple_tree &&_other) : d_v_(std::move(_other.d_v_)) {}

    simple_tree &operator=(const simple_tree &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    simple_tree &operator=(simple_tree &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) simple_tree clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<SLeaf>(_sv.v())) {
        const auto &[d_a0] = std::get<SLeaf>(_sv.v());
        return simple_tree(SLeaf{d_a0});
      } else {
        const auto &[d_a0, d_a1] = std::get<SNode>(_sv.v());
        return simple_tree(SNode{
            d_a0 ? std::make_unique<LoopifyTrees::simple_tree>(d_a0->clone())
                 : nullptr,
            d_a1 ? std::make_unique<LoopifyTrees::simple_tree>(d_a1->clone())
                 : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static simple_tree sleaf(unsigned int a0) {
      return simple_tree(SLeaf{std::move(a0)});
    }

    __attribute__((pure)) static simple_tree snode(const simple_tree &a0,
                                                   const simple_tree &a1) {
      return simple_tree(SNode{std::make_unique<simple_tree>(a0),
                               std::make_unique<simple_tree>(a1)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    /// count_paths_simple t n counts paths with sum n (simpler variant).
    __attribute__((pure)) unsigned int
    count_paths_simple(const unsigned int &n) const {
      const simple_tree *_self = this;

      struct _Enter {
        const simple_tree *_self;
        const unsigned int n;
      };

      struct _Call1 {
        simple_tree *_s0;
        decltype((((std::declval<const unsigned int &>() - 1u) >
                           std::declval<const unsigned int &>()
                       ? 0
                       : (std::declval<const unsigned int &>() - 1u)))) _s1;
      };

      struct _Call2 {
        unsigned int _s0;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self, n});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const simple_tree *_self = _f._self;
          const unsigned int n = _f.n;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename simple_tree::SLeaf>(_sv.v())) {
            const auto &[d_a0] = std::get<typename simple_tree::SLeaf>(_sv.v());
            if (d_a0 == n) {
              _result = 1u;
            } else {
              _result = 0u;
            }
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename simple_tree::SNode>(_sv.v());
            if (n <= 0u) {
              _result = 0u;
            } else {
              _stack.emplace_back(
                  _Call1{d_a0.get(), (((n - 1u) > n ? 0 : (n - 1u)))});
              _stack.emplace_back(
                  _Enter{d_a1.get(), (((n - 1u) > n ? 0 : (n - 1u)))});
            }
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result});
          _stack.emplace_back(_Enter{_f._s0, _f._s1});
        } else {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = (_result + _f._s0);
        }
      }
      return _result;
    }

    /// simple_tree_sum t sums all leaf values.
    __attribute__((pure)) unsigned int simple_tree_sum() const {
      const simple_tree *_self = this;

      struct _Enter {
        const simple_tree *_self;
      };

      struct _Call1 {
        simple_tree *_s0;
      };

      struct _Call2 {
        unsigned int _s0;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const simple_tree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename simple_tree::SLeaf>(_sv.v())) {
            const auto &[d_a0] = std::get<typename simple_tree::SLeaf>(_sv.v());
            _result = d_a0;
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename simple_tree::SNode>(_sv.v());
            _stack.emplace_back(_Call1{d_a0.get()});
            _stack.emplace_back(_Enter{d_a1.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = (_result + _f._s0);
        }
      }
      return _result;
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, simple_tree, T1, simple_tree, T1> F1>
    T1 simple_tree_rec(F0 &&f, F1 &&f0) const {
      const simple_tree *_self = this;

      struct _Enter {
        const simple_tree *_self;
      };

      struct _Call1 {
        simple_tree *_s0;
        simple_tree _s1;
        simple_tree _s2;
      };

      struct _Call2 {
        T1 _s0;
        simple_tree _s1;
        simple_tree _s2;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const simple_tree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename simple_tree::SLeaf>(_sv.v())) {
            const auto &[d_a0] = std::get<typename simple_tree::SLeaf>(_sv.v());
            _result = f(d_a0);
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename simple_tree::SNode>(_sv.v());
            _stack.emplace_back(_Call1{d_a0.get(), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a1.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = f0(_f._s2, _result, _f._s1, _f._s0);
        }
      }
      return _result;
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, simple_tree, T1, simple_tree, T1> F1>
    T1 simple_tree_rect(F0 &&f, F1 &&f0) const {
      const simple_tree *_self = this;

      struct _Enter {
        const simple_tree *_self;
      };

      struct _Call1 {
        simple_tree *_s0;
        simple_tree _s1;
        simple_tree _s2;
      };

      struct _Call2 {
        T1 _s0;
        simple_tree _s1;
        simple_tree _s2;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const simple_tree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename simple_tree::SLeaf>(_sv.v())) {
            const auto &[d_a0] = std::get<typename simple_tree::SLeaf>(_sv.v());
            _result = f(d_a0);
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename simple_tree::SNode>(_sv.v());
            _stack.emplace_back(_Call1{d_a0.get(), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a1.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = f0(_f._s2, _result, _f._s1, _f._s0);
        }
      }
      return _result;
    }
  };

  /// Helper: compute minimum of three values.
  __attribute__((pure)) static unsigned int min3(unsigned int a, unsigned int b,
                                                 unsigned int c);
  /// Helper: compute maximum of three values.
  __attribute__((pure)) static unsigned int max3(unsigned int a, unsigned int b,
                                                 unsigned int c);
  /// tree_min_max t finds minimum and maximum values in tree.
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  tree_min_max(const tree<unsigned int> &t);
  /// all_paths_sum t sums all root-to-leaf path sums.
  __attribute__((pure)) static unsigned int
  all_paths_sum(const tree<unsigned int> &t);
  /// tree_contains x t checks if value exists in tree.
  __attribute__((pure)) static bool tree_contains(const unsigned int &x,
                                                  const tree<unsigned int> &t);
};

#endif // INCLUDED_LOOPIFY_TREES
