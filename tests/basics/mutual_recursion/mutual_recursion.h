#ifndef INCLUDED_MUTUAL_RECURSION
#define INCLUDED_MUTUAL_RECURSION

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MutualRecursion {
  static bool is_even(unsigned int n);
  static bool is_odd(unsigned int n);
  template <typename A> struct tree;
  template <typename A> struct forest;

  template <typename A> struct tree {
    // TYPES
    struct Leaf {
      A a0;
    };

    struct Node {
      std::unique_ptr<forest<A>> a0;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Leaf _v) : v_(std::move(_v)) {}

    explicit tree(Node _v) : v_(std::move(_v)) {}

    tree(const tree<A> &_other) : v_(std::move(_other.clone().v_)) {}

    tree(tree<A> &&_other) : v_(std::move(_other.v_)) {}

    tree<A> &operator=(const tree<A> &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    tree<A> &operator=(tree<A> &&_other) {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    tree<A> clone() const {
      if (std::holds_alternative<Leaf>(this->v())) {
        const auto &[a0] = std::get<Leaf>(this->v());
        return tree<A>(Leaf{a0});
      } else {
        const auto &[a0] = std::get<Node>(this->v());
        return tree<A>(
            Node{a0 ? std::make_unique<MutualRecursion::forest<A>>(a0->clone())
                    : nullptr});
      }
    }

    // CREATORS
    template <typename _U> explicit tree(const tree<_U> &_other) {
      if (std::holds_alternative<typename tree<_U>::Leaf>(_other.v())) {
        const auto &[a0] = std::get<typename tree<_U>::Leaf>(_other.v());
        this->v_ = Leaf{A(a0)};
      } else {
        const auto &[a0] = std::get<typename tree<_U>::Node>(_other.v());
        this->v_ = Node{a0 ? std::make_unique<MutualRecursion::forest<A>>(*a0)
                           : nullptr};
      }
    }

    static tree<A> leaf(A a0) { return tree(Leaf{std::move(a0)}); }

    static tree<A> node(forest<A> a0) {
      return tree(Node{std::make_unique<forest<A>>(std::move(a0))});
    }

    // MANIPULATORS
    ~tree() {
      std::vector<std::unique_ptr<tree<A>>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](tree<A> &_node) {
        if (std::holds_alternative<Node>(_node.v_)) {
          auto &_alt = std::get<Node>(_node.v_);
          if (_alt.a0) {
            if (std::holds_alternative<
                    typename MutualRecursion::forest<A>::Trees>(_alt.a0->v())) {
              auto &_palt =
                  std::get<typename MutualRecursion::forest<A>::Trees>(
                      _alt.a0->v_mut());
              if (_palt.a0) {
                _stack.push_back(std::move(_palt.a0));
              }
            }
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
  };

  template <typename A> struct forest {
    // TYPES
    struct Empty {};

    struct Trees {
      std::unique_ptr<tree<A>> a0;
      std::unique_ptr<forest<A>> a1;
    };

    using variant_t = std::variant<Empty, Trees>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    forest() {}

    explicit forest(Empty _v) : v_(_v) {}

    explicit forest(Trees _v) : v_(std::move(_v)) {}

    forest(const forest<A> &_other) : v_(std::move(_other.clone().v_)) {}

    forest(forest<A> &&_other) : v_(std::move(_other.v_)) {}

    forest<A> &operator=(const forest<A> &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    forest<A> &operator=(forest<A> &&_other) {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    forest<A> clone() const {
      forest<A> _out{};

      struct _CloneFrame {
        const forest<A> *_src;
        forest<A> *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const forest<A> *_src = _frame._src;
        forest<A> *_dst = _frame._dst;
        if (std::holds_alternative<Empty>(_src->v())) {
          _dst->v_ = Empty{};
        } else {
          const auto &_alt = std::get<Trees>(_src->v());
          _dst->v_ = Trees{_alt.a0 ? std::make_unique<MutualRecursion::tree<A>>(
                                         _alt.a0->clone())
                                   : nullptr,
                           _alt.a1 ? std::make_unique<forest<A>>() : nullptr};
          auto &_dst_alt = std::get<Trees>(_dst->v_);
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    template <typename _U> explicit forest(const forest<_U> &_other) {
      if (std::holds_alternative<typename forest<_U>::Empty>(_other.v())) {
        this->v_ = Empty{};
      } else {
        const auto &[a0, a1] = std::get<typename forest<_U>::Trees>(_other.v());
        this->v_ = Trees{a0 ? std::make_unique<MutualRecursion::tree<A>>(*a0)
                            : nullptr,
                         a1 ? std::make_unique<forest<A>>(*a1) : nullptr};
      }
    }

    static forest<A> empty() { return forest(Empty{}); }

    static forest<A> trees(tree<A> a0, forest<A> a1) {
      return forest(Trees{std::make_unique<tree<A>>(std::move(a0)),
                          std::make_unique<forest<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~forest() {
      std::vector<std::unique_ptr<forest<A>>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](forest<A> &_node) {
        if (std::holds_alternative<Trees>(_node.v_)) {
          auto &_alt = std::get<Trees>(_node.v_);
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
  };

  template <typename T1, typename T2, typename F0, typename F1>
    requires std::is_invocable_r_v<T2, F0 &, T1 &> &&
             std::is_invocable_r_v<T2, F1 &, forest<T1> &>
  static T2 tree_rect(F0 &&f, F1 &&f0, const tree<T1> &t) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
      const auto &[a0] = std::get<typename tree<T1>::Leaf>(t.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename tree<T1>::Node>(t.v());
      return f0(*a0);
    }
  }

  template <typename T1, typename T2, typename F0, typename F1>
    requires std::is_invocable_r_v<T2, F0 &, T1 &> &&
             std::is_invocable_r_v<T2, F1 &, forest<T1> &>
  static T2 tree_rec(F0 &&f, F1 &&f0, const tree<T1> &t) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
      const auto &[a0] = std::get<typename tree<T1>::Leaf>(t.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename tree<T1>::Node>(t.v());
      return f0(*a0);
    }
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, tree<T1> &, forest<T1> &, T2 &>
  static T2 forest_rect(T2 f, F1 &&f0, const forest<T1> &f1) {
    if (std::holds_alternative<typename forest<T1>::Empty>(f1.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename forest<T1>::Trees>(f1.v());
      return f0(*a0, *a1, forest_rect<T1, T2>(f, f0, *a1));
    }
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, tree<T1> &, forest<T1> &, T2 &>
  static T2 forest_rec(T2 f, F1 &&f0, const forest<T1> &f1) {
    if (std::holds_alternative<typename forest<T1>::Empty>(f1.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename forest<T1>::Trees>(f1.v());
      return f0(*a0, *a1, forest_rec<T1, T2>(f, f0, *a1));
    }
  }

  template <typename T1> static unsigned int tree_size(const tree<T1> &t) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
      return 1u;
    } else {
      const auto &[a0] = std::get<typename tree<T1>::Node>(t.v());
      return forest_size<T1>(*a0);
    }
  }

  template <typename T1> static unsigned int forest_size(const forest<T1> &f) {
    if (std::holds_alternative<typename forest<T1>::Empty>(f.v())) {
      return 0u;
    } else {
      const auto &[a0, a1] = std::get<typename forest<T1>::Trees>(f.v());
      return (tree_size<T1>(*a0) + forest_size<T1>(*a1));
    }
  }

  static unsigned int tree_sum(const tree<unsigned int> &t);
  static unsigned int forest_sum(const forest<unsigned int> &f);
  static inline const bool test_even_0 = is_even(0u);
  static inline const bool test_even_4 = is_even(4u);
  static inline const bool test_odd_3 = is_odd(3u);
  static inline const bool test_odd_4 = is_odd(4u);
  static inline const tree<unsigned int> simple_tree =
      tree<unsigned int>::node(forest<unsigned int>::trees(
          tree<unsigned int>::leaf(1u),
          forest<unsigned int>::trees(tree<unsigned int>::leaf(2u),
                                      forest<unsigned int>::empty())));
  static inline const tree<unsigned int> nested_tree =
      tree<unsigned int>::node(forest<unsigned int>::trees(
          tree<unsigned int>::node(forest<unsigned int>::trees(
              tree<unsigned int>::leaf(3u), forest<unsigned int>::empty())),
          forest<unsigned int>::trees(tree<unsigned int>::leaf(4u),
                                      forest<unsigned int>::empty())));
  static inline const unsigned int test_size_simple =
      tree_size<unsigned int>(simple_tree);
  static inline const unsigned int test_size_nested =
      tree_size<unsigned int>(nested_tree);
  static inline const unsigned int test_sum_simple = tree_sum(simple_tree);
  static inline const unsigned int test_sum_nested = tree_sum(nested_tree);
};

#endif // INCLUDED_MUTUAL_RECURSION
