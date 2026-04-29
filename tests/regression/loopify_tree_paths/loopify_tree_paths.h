#ifndef INCLUDED_LOOPIFY_TREE_PATHS
#define INCLUDED_LOOPIFY_TREE_PATHS

#include <algorithm>
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

  __attribute__((pure)) static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons{std::move(a0), std::make_unique<List<t_A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List>> _stack;
    auto _drain = [&](List &_node) {
      if (std::holds_alternative<Cons>(_node.d_v_)) {
        auto &_alt = std::get<Cons>(_node.d_v_);
        if (_alt.d_a1)
          _stack.push_back(std::move(_alt.d_a1));
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node)
        _drain(*_node);
    }
  }

  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) List<t_A> app(List<t_A> m) const {
    std::unique_ptr<List<t_A>> _head{};
    std::unique_ptr<List<t_A>> *_write = &_head;
    const List *_loop_self = this;
    List<t_A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *(_loop_self);
      if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
        *(_write) = std::make_unique<List<t_A>>(std::move(_loop_m));
        break;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
        auto _cell = std::make_unique<List<t_A>>(
            typename List<t_A>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write = &std::get<typename List<t_A>::Cons>((*_write)->v_mut()).d_a1;
        const List *_next_self = d_a1.get();
        List<t_A> _next_m = std::move(_loop_m);
        _loop_self = std::move(_next_self);
        _loop_m = std::move(_next_m);
        continue;
      }
    }
    return std::move(*(_head));
  }
};

struct LoopifyTreePaths {
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
    __attribute__((pure)) tree clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Leaf>(_sv.v())) {
        return tree(Leaf{});
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<Node>(_sv.v());
        return tree(
            Node{d_a0 ? std::make_unique<LoopifyTreePaths::tree>(d_a0->clone())
                      : nullptr,
                 d_a1,
                 d_a2 ? std::make_unique<LoopifyTreePaths::tree>(d_a2->clone())
                      : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static tree leaf() { return tree(Leaf{}); }

    __attribute__((pure)) static tree node(tree a0, unsigned int a1, tree a2) {
      return tree(Node{std::make_unique<tree>(std::move(a0)), std::move(a1),
                       std::make_unique<tree>(std::move(a2))});
    }

    // MANIPULATORS
    ~tree() {
      std::vector<std::unique_ptr<tree>> _stack;
      auto _drain = [&](tree &_node) {
        if (std::holds_alternative<Node>(_node.d_v_)) {
          auto &_alt = std::get<Node>(_node.d_v_);
          if (_alt.d_a0)
            _stack.push_back(std::move(_alt.d_a0));
          if (_alt.d_a2)
            _stack.push_back(std::move(_alt.d_a2));
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node)
          _drain(*_node);
      }
    }

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) List<unsigned int> flatten_paths() const {
      const tree *_self = this;

      struct _Enter {
        const tree *_self;
      };

      struct _Call1 {
        tree *_s0;
        unsigned int _s1;
      };

      struct _Call2 {
        List<unsigned int> _s0;
        unsigned int _s1;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      List<unsigned int> _result{};
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
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = List<unsigned int>::nil();
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_Call1{d_a0.get(), d_a1});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result, _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = List<unsigned int>::cons(_f._s1, _result.app(_f._s0));
        }
      }
      return _result;
    }

    __attribute__((pure)) unsigned int max_path_sum() const {
      const tree *_self = this;

      struct _Enter {
        const tree *_self;
      };

      struct _Call1 {
        tree *_s0;
        unsigned int _s1;
      };

      struct _Call2 {
        unsigned int _s0;
        unsigned int _s1;
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
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = 0u;
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_Call1{d_a0.get(), d_a1});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result, _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = (_f._s1 + std::max(_result, _f._s0));
        }
      }
      return _result;
    }

    __attribute__((pure)) std::optional<List<unsigned int>>
    find_path_sum(const unsigned int &acc, const unsigned int &target) const {
      const tree *_self = this;
      auto &&_sv = *(_self);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        if (acc == target) {
          return std::make_optional<List<unsigned int>>(
              List<unsigned int>::nil());
        } else {
          return std::optional<List<unsigned int>>();
        }
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(_sv.v());
        unsigned int new_acc = (acc + d_a1);
        auto _cs = (*(d_a0)).find_path_sum(new_acc, target);
        if (_cs.has_value()) {
          const List<unsigned int> &path = *_cs;
          return std::make_optional<List<unsigned int>>(
              List<unsigned int>::cons(d_a1, path));
        } else {
          auto _cs1 = (*(d_a2)).find_path_sum(new_acc, target);
          if (_cs1.has_value()) {
            const List<unsigned int> &path = *_cs1;
            return std::make_optional<List<unsigned int>>(
                List<unsigned int>::cons(d_a1, path));
          } else {
            return std::optional<List<unsigned int>>();
          }
        }
      }
    }

    __attribute__((pure)) unsigned int
    count_paths_sum(const unsigned int &target) const {
      return (*(this)).count_paths_sum_aux(0u, target);
    }

    __attribute__((pure)) unsigned int
    count_paths_sum_aux(const unsigned int &acc,
                        const unsigned int &target) const {
      const tree *_self = this;

      struct _Enter {
        const tree *_self;
        const unsigned int acc;
      };

      struct _Call1 {
        tree *_s0;
        unsigned int _s1;
      };

      struct _Call2 {
        unsigned int _s0;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self, acc});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          const unsigned int acc = _f.acc;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            if (acc == target) {
              _result = 1u;
            } else {
              _result = 0u;
            }
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename tree::Node>(_sv.v());
            unsigned int new_acc = (acc + d_a1);
            _stack.emplace_back(_Call1{d_a0.get(), new_acc});
            _stack.emplace_back(_Enter{d_a2.get(), new_acc});
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

    __attribute__((pure)) List<List<unsigned int>> paths() const {
      const tree *_self = this;

      struct _Enter {
        const tree *_self;
      };

      struct _Call1 {
        tree *_s0;
        unsigned int _s1;
        unsigned int _s2;
      };

      struct _Call2 {
        List<List<unsigned int>> _s0;
        unsigned int _s1;
        unsigned int _s2;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      List<List<unsigned int>> _result{};
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
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = List<List<unsigned int>>::cons(
                List<unsigned int>::nil(), List<List<unsigned int>>::nil());
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_Call1{d_a0.get(), d_a1, d_a1});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = map_cons(_f._s2, _result).app(map_cons(_f._s1, _f._s0));
        }
      }
      return _result;
    }

    template <typename T1, MapsTo<T1, tree, T1, unsigned int, tree, T1> F1>
    T1 tree_rec(const T1 f, F1 &&f0) const {
      const tree *_self = this;

      struct _Enter {
        const tree *_self;
      };

      struct _Call1 {
        tree *_s0;
        tree _s1;
        unsigned int _s2;
        tree _s3;
      };

      struct _Call2 {
        T1 _s0;
        tree _s1;
        unsigned int _s2;
        tree _s3;
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
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename tree::Node>(_sv.v());
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

    template <typename T1, MapsTo<T1, tree, T1, unsigned int, tree, T1> F1>
    T1 tree_rect(const T1 f, F1 &&f0) const {
      const tree *_self = this;

      struct _Enter {
        const tree *_self;
      };

      struct _Call1 {
        tree *_s0;
        tree _s1;
        unsigned int _s2;
        tree _s3;
      };

      struct _Call2 {
        T1 _s0;
        tree _s1;
        unsigned int _s2;
        tree _s3;
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
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename tree::Node>(_sv.v());
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

  __attribute__((pure)) static List<List<unsigned int>>
  map_cons(unsigned int x, const List<List<unsigned int>> &ll);

  struct bool_tree {
    // TYPES
    struct BLeaf {
      unsigned int d_a0;
    };

    struct BNode {
      std::unique_ptr<bool_tree> d_a0;
      std::unique_ptr<bool_tree> d_a1;
    };

    using variant_t = std::variant<BLeaf, BNode>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    bool_tree() {}

    explicit bool_tree(BLeaf _v) : d_v_(std::move(_v)) {}

    explicit bool_tree(BNode _v) : d_v_(std::move(_v)) {}

    bool_tree(const bool_tree &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    bool_tree(bool_tree &&_other) : d_v_(std::move(_other.d_v_)) {}

    bool_tree &operator=(const bool_tree &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    bool_tree &operator=(bool_tree &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) bool_tree clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<BLeaf>(_sv.v())) {
        const auto &[d_a0] = std::get<BLeaf>(_sv.v());
        return bool_tree(BLeaf{d_a0});
      } else {
        const auto &[d_a0, d_a1] = std::get<BNode>(_sv.v());
        return bool_tree(BNode{
            d_a0 ? std::make_unique<LoopifyTreePaths::bool_tree>(d_a0->clone())
                 : nullptr,
            d_a1 ? std::make_unique<LoopifyTreePaths::bool_tree>(d_a1->clone())
                 : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static bool_tree bleaf(unsigned int a0) {
      return bool_tree(BLeaf{std::move(a0)});
    }

    __attribute__((pure)) static bool_tree bnode(bool_tree a0, bool_tree a1) {
      return bool_tree(BNode{std::make_unique<bool_tree>(std::move(a0)),
                             std::make_unique<bool_tree>(std::move(a1))});
    }

    // MANIPULATORS
    ~bool_tree() {
      std::vector<std::unique_ptr<bool_tree>> _stack;
      auto _drain = [&](bool_tree &_node) {
        if (std::holds_alternative<BNode>(_node.d_v_)) {
          auto &_alt = std::get<BNode>(_node.d_v_);
          if (_alt.d_a0)
            _stack.push_back(std::move(_alt.d_a0));
          if (_alt.d_a1)
            _stack.push_back(std::move(_alt.d_a1));
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node)
          _drain(*_node);
      }
    }

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <MapsTo<bool, unsigned int> F0>
    __attribute__((pure)) bool and_search(F0 &&p) const {
      const bool_tree *_self = this;

      struct _Enter {
        const bool_tree *_self;
      };

      struct _Call1 {
        bool_tree *_s0;
      };

      struct _Call2 {
        bool _s0;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      bool _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const bool_tree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename bool_tree::BLeaf>(_sv.v())) {
            const auto &[d_a0] = std::get<typename bool_tree::BLeaf>(_sv.v());
            _result = p(d_a0);
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename bool_tree::BNode>(_sv.v());
            _stack.emplace_back(_Call1{d_a0.get()});
            _stack.emplace_back(_Enter{d_a1.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = (_result && _f._s0);
        }
      }
      return _result;
    }

    template <MapsTo<bool, unsigned int> F0>
    __attribute__((pure)) bool or_search(F0 &&p) const {
      const bool_tree *_self = this;

      struct _Enter {
        const bool_tree *_self;
      };

      struct _Call1 {
        bool_tree *_s0;
      };

      struct _Call2 {
        bool _s0;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2>;
      bool _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const bool_tree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename bool_tree::BLeaf>(_sv.v())) {
            const auto &[d_a0] = std::get<typename bool_tree::BLeaf>(_sv.v());
            _result = p(d_a0);
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename bool_tree::BNode>(_sv.v());
            _stack.emplace_back(_Call1{d_a0.get()});
            _stack.emplace_back(_Enter{d_a1.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = (_result || _f._s0);
        }
      }
      return _result;
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, bool_tree, T1, bool_tree, T1> F1>
    T1 bool_tree_rec(F0 &&f, F1 &&f0) const {
      const bool_tree *_self = this;

      struct _Enter {
        const bool_tree *_self;
      };

      struct _Call1 {
        bool_tree *_s0;
        bool_tree _s1;
        bool_tree _s2;
      };

      struct _Call2 {
        T1 _s0;
        bool_tree _s1;
        bool_tree _s2;
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
          const bool_tree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename bool_tree::BLeaf>(_sv.v())) {
            const auto &[d_a0] = std::get<typename bool_tree::BLeaf>(_sv.v());
            _result = f(d_a0);
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename bool_tree::BNode>(_sv.v());
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
              MapsTo<T1, bool_tree, T1, bool_tree, T1> F1>
    T1 bool_tree_rect(F0 &&f, F1 &&f0) const {
      const bool_tree *_self = this;

      struct _Enter {
        const bool_tree *_self;
      };

      struct _Call1 {
        bool_tree *_s0;
        bool_tree _s1;
        bool_tree _s2;
      };

      struct _Call2 {
        T1 _s0;
        bool_tree _s1;
        bool_tree _s2;
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
          const bool_tree *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename bool_tree::BLeaf>(_sv.v())) {
            const auto &[d_a0] = std::get<typename bool_tree::BLeaf>(_sv.v());
            _result = f(d_a0);
          } else {
            const auto &[d_a0, d_a1] =
                std::get<typename bool_tree::BNode>(_sv.v());
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
};

#endif // INCLUDED_LOOPIFY_TREE_PATHS
