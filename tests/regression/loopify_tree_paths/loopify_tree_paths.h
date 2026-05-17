#ifndef INCLUDED_LOOPIFY_TREE_PATHS
#define INCLUDED_LOOPIFY_TREE_PATHS

#include <algorithm>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a0;
    std::unique_ptr<List<A>> a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  List(const List<A> &_other) : v_(std::move(_other.clone().v_)) {}

  List(List<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  List<A> clone() const {
    List<A> _out{};

    struct _CloneFrame {
      const List<A> *_src;
      List<A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<A> *_src = _frame._src;
      List<A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->v_ =
            Cons{_alt.a0, _alt.a1 ? std::make_unique<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.a1) {
          _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a0, a1] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a0), a1 ? std::make_unique<List<A>>(*a1) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a0, List<A> a1) {
    return List(Cons{std::move(a0), std::make_unique<List<A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
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

  List<A> app(List<A> m) const {
    std::unique_ptr<List<A>> _head{};
    std::unique_ptr<List<A>> *_write = &_head;
    const List *_loop_self = this;
    List<A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        *_write = std::make_unique<List<A>>(std::move(_loop_m));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell =
            std::make_unique<List<A>>(typename List<A>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<A>::Cons>((*_write)->v_mut()).a1;
        _loop_self = a1.get();
        continue;
      }
    }
    return std::move(*_head);
  }
};

struct LoopifyTreePaths {
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::unique_ptr<tree> a0;
      unsigned int a1;
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

    static tree node(tree a0, unsigned int a1, tree a2) {
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

    List<unsigned int> flatten_paths() const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _After_Node: saves [_s0, a1], dispatches next recursive call.
      struct _After_Node {
        tree *_s0;
        unsigned int a1;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        List<unsigned int> _result;
        unsigned int a1;
      };

      using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
      List<unsigned int> _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified flatten_paths: _Enter -> _After_Node -> _Combine_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = List<unsigned int>::nil();
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_After_Node{a0.get(), a1});
            _stack.emplace_back(_Enter{a2.get()});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{std::move(_result), _f.a1});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = List<unsigned int>::cons(_f.a1, _result.app(_f._result));
        }
      }
      return _result;
    }

    unsigned int max_path_sum() const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _After_Node: saves [_s0, a1], dispatches next recursive call.
      struct _After_Node {
        tree *_s0;
        unsigned int a1;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        unsigned int _result;
        unsigned int a1;
      };

      using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified max_path_sum: _Enter -> _After_Node -> _Combine_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = 0u;
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
          _result = (_f.a1 + std::max(_result, _f._result));
        }
      }
      return _result;
    }

    std::optional<List<unsigned int>> find_path_sum(unsigned int acc,
                                                    unsigned int target) const {
      const tree *_self = this;
      auto &&_sv = *_self;
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        if (acc == target) {
          return std::make_optional<List<unsigned int>>(
              List<unsigned int>::nil());
        } else {
          return std::optional<List<unsigned int>>();
        }
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
        unsigned int new_acc = (acc + a1);
        auto _cs = (*a0).find_path_sum(new_acc, target);
        if (_cs.has_value()) {
          const List<unsigned int> &path = *_cs;
          return std::make_optional<List<unsigned int>>(
              List<unsigned int>::cons(a1, path));
        } else {
          auto _cs1 = (*a2).find_path_sum(new_acc, target);
          if (_cs1.has_value()) {
            const List<unsigned int> &path = *_cs1;
            return std::make_optional<List<unsigned int>>(
                List<unsigned int>::cons(a1, path));
          } else {
            return std::optional<List<unsigned int>>();
          }
        }
      }
    }

    unsigned int count_paths_sum(unsigned int target) const {
      return (*this).count_paths_sum_aux(0u, target);
    }

    unsigned int count_paths_sum_aux(unsigned int acc,
                                     unsigned int target) const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
        unsigned int acc;
      };

      /// _After_Node: saves [_s0, new_acc], dispatches next recursive call.
      struct _After_Node {
        tree *_s0;
        unsigned int new_acc;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        unsigned int _result;
      };

      using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self, acc});
      /// Loopified count_paths_sum_aux: _Enter -> _After_Node -> _Combine_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          unsigned int acc = _f.acc;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            if (acc == target) {
              _result = 1u;
            } else {
              _result = 0u;
            }
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            unsigned int new_acc = (acc + a1);
            _stack.emplace_back(_After_Node{a0.get(), new_acc});
            _stack.emplace_back(_Enter{a2.get(), new_acc});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{_result});
          _stack.emplace_back(_Enter{_f._s0, _f.new_acc});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = (_result + _f._result);
        }
      }
      return _result;
    }

    List<List<unsigned int>> paths() const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _After_Node: saves [_s0, a1_0, a1_1], dispatches next recursive call.
      struct _After_Node {
        tree *_s0;
        unsigned int a1_0;
        unsigned int a1_1;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        List<List<unsigned int>> _result;
        unsigned int a1_0;
        unsigned int a1_1;
      };

      using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
      List<List<unsigned int>> _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified paths: _Enter -> _After_Node -> _Combine_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = List<List<unsigned int>>::cons(
                List<unsigned int>::nil(), List<List<unsigned int>>::nil());
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_After_Node{a0.get(), a1, a1});
            _stack.emplace_back(_Enter{a2.get()});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(
              _Combine_Node{std::move(_result), _f.a1_0, _f.a1_1});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result =
              map_cons(_f.a1_1, _result).app(map_cons(_f.a1_0, _f._result));
        }
      }
      return _result;
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

      /// _After_Node: saves [_s0, a2, a1, a0], dispatches next recursive call.
      struct _After_Node {
        tree *_s0;
        tree a2;
        unsigned int a1;
        tree a0;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        T1 _result;
        tree a2;
        unsigned int a1;
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
            _result = f;
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
      requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, unsigned int &,
                                     tree &, T1 &>
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
        unsigned int a1;
        tree a0;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        T1 _result;
        tree a2;
        unsigned int a1;
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
            _result = f;
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

  static List<List<unsigned int>> map_cons(unsigned int x,
                                           const List<List<unsigned int>> &ll);

  struct bool_tree {
    // TYPES
    struct BLeaf {
      unsigned int a0;
    };

    struct BNode {
      std::unique_ptr<bool_tree> a0;
      std::unique_ptr<bool_tree> a1;
    };

    using variant_t = std::variant<BLeaf, BNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    bool_tree() {}

    explicit bool_tree(BLeaf _v) : v_(std::move(_v)) {}

    explicit bool_tree(BNode _v) : v_(std::move(_v)) {}

    bool_tree(const bool_tree &_other) : v_(std::move(_other.clone().v_)) {}

    bool_tree(bool_tree &&_other) noexcept : v_(std::move(_other.v_)) {}

    bool_tree &operator=(const bool_tree &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    bool_tree &operator=(bool_tree &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    bool_tree clone() const {
      bool_tree _out{};

      struct _CloneFrame {
        const bool_tree *_src;
        bool_tree *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const bool_tree *_src = _frame._src;
        bool_tree *_dst = _frame._dst;
        if (std::holds_alternative<BLeaf>(_src->v())) {
          const auto &_alt = std::get<BLeaf>(_src->v());
          _dst->v_ = BLeaf{_alt.a0};
        } else {
          const auto &_alt = std::get<BNode>(_src->v());
          _dst->v_ = BNode{_alt.a0 ? std::make_unique<bool_tree>() : nullptr,
                           _alt.a1 ? std::make_unique<bool_tree>() : nullptr};
          auto &_dst_alt = std::get<BNode>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static bool_tree bleaf(unsigned int a0) { return bool_tree(BLeaf{a0}); }

    static bool_tree bnode(bool_tree a0, bool_tree a1) {
      return bool_tree(BNode{std::make_unique<bool_tree>(std::move(a0)),
                             std::make_unique<bool_tree>(std::move(a1))});
    }

    // MANIPULATORS
    ~bool_tree() {
      std::vector<std::unique_ptr<bool_tree>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](bool_tree &_node) {
        if (std::holds_alternative<BNode>(_node.v_)) {
          auto &_alt = std::get<BNode>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
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

    template <typename F0>
      requires std::is_invocable_r_v<bool, F0 &, unsigned int &>
    bool and_search(F0 &&p) const {
      const bool_tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const bool_tree *_self;
      };

      /// _After_BNode: saves [_s0], dispatches next recursive call.
      struct _After_BNode {
        bool_tree *_s0;
      };

      /// _Combine_BNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_BNode {
        bool _result;
      };

      using _Frame = std::variant<_Enter, _After_BNode, _Combine_BNode>;
      bool _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified and_search: _Enter -> _After_BNode -> _Combine_BNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const bool_tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename bool_tree::BLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename bool_tree::BLeaf>(_sv.v());
            _result = p(a0);
          } else {
            const auto &[a0, a1] = std::get<typename bool_tree::BNode>(_sv.v());
            _stack.emplace_back(_After_BNode{a0.get()});
            _stack.emplace_back(_Enter{a1.get()});
          }
        } else if (std::holds_alternative<_After_BNode>(_frame)) {
          auto _f = std::move(std::get<_After_BNode>(_frame));
          _stack.emplace_back(_Combine_BNode{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_BNode>(_frame));
          _result = (_result && _f._result);
        }
      }
      return _result;
    }

    template <typename F0>
      requires std::is_invocable_r_v<bool, F0 &, unsigned int &>
    bool or_search(F0 &&p) const {
      const bool_tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const bool_tree *_self;
      };

      /// _After_BNode: saves [_s0], dispatches next recursive call.
      struct _After_BNode {
        bool_tree *_s0;
      };

      /// _Combine_BNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_BNode {
        bool _result;
      };

      using _Frame = std::variant<_Enter, _After_BNode, _Combine_BNode>;
      bool _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified or_search: _Enter -> _After_BNode -> _Combine_BNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const bool_tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename bool_tree::BLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename bool_tree::BLeaf>(_sv.v());
            _result = p(a0);
          } else {
            const auto &[a0, a1] = std::get<typename bool_tree::BNode>(_sv.v());
            _stack.emplace_back(_After_BNode{a0.get()});
            _stack.emplace_back(_Enter{a1.get()});
          }
        } else if (std::holds_alternative<_After_BNode>(_frame)) {
          auto _f = std::move(std::get<_After_BNode>(_frame));
          _stack.emplace_back(_Combine_BNode{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_BNode>(_frame));
          _result = (_result || _f._result);
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
               std::is_invocable_r_v<T1, F1 &, bool_tree &, T1 &, bool_tree &,
                                     T1 &>
    T1 bool_tree_rec(F0 &&f, F1 &&f0) const {
      const bool_tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const bool_tree *_self;
      };

      /// _After_BNode: saves [_s0, a1, a0], dispatches next recursive call.
      struct _After_BNode {
        bool_tree *_s0;
        bool_tree a1;
        bool_tree a0;
      };

      /// _Combine_BNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_BNode {
        T1 _result;
        bool_tree a1;
        bool_tree a0;
      };

      using _Frame = std::variant<_Enter, _After_BNode, _Combine_BNode>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified bool_tree_rec: _Enter -> _After_BNode -> _Combine_BNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const bool_tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename bool_tree::BLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename bool_tree::BLeaf>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1] = std::get<typename bool_tree::BNode>(_sv.v());
            _stack.emplace_back(_After_BNode{a0.get(), *a1, *a0});
            _stack.emplace_back(_Enter{a1.get()});
          }
        } else if (std::holds_alternative<_After_BNode>(_frame)) {
          auto _f = std::move(std::get<_After_BNode>(_frame));
          _stack.emplace_back(
              _Combine_BNode{_result, std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_BNode>(_frame));
          _result = f0(_f.a0, _result, _f.a1, _f._result);
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, unsigned int &> &&
               std::is_invocable_r_v<T1, F1 &, bool_tree &, T1 &, bool_tree &,
                                     T1 &>
    T1 bool_tree_rect(F0 &&f, F1 &&f0) const {
      const bool_tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const bool_tree *_self;
      };

      /// _After_BNode: saves [_s0, a1, a0], dispatches next recursive call.
      struct _After_BNode {
        bool_tree *_s0;
        bool_tree a1;
        bool_tree a0;
      };

      /// _Combine_BNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_BNode {
        T1 _result;
        bool_tree a1;
        bool_tree a0;
      };

      using _Frame = std::variant<_Enter, _After_BNode, _Combine_BNode>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified bool_tree_rect: _Enter -> _After_BNode -> _Combine_BNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const bool_tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename bool_tree::BLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename bool_tree::BLeaf>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1] = std::get<typename bool_tree::BNode>(_sv.v());
            _stack.emplace_back(_After_BNode{a0.get(), *a1, *a0});
            _stack.emplace_back(_Enter{a1.get()});
          }
        } else if (std::holds_alternative<_After_BNode>(_frame)) {
          auto _f = std::move(std::get<_After_BNode>(_frame));
          _stack.emplace_back(
              _Combine_BNode{_result, std::move(_f.a1), std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_BNode>(_frame));
          _result = f0(_f.a0, _result, _f.a1, _f._result);
        }
      }
      return _result;
    }
  };
};

#endif // INCLUDED_LOOPIFY_TREE_PATHS
