#ifndef INCLUDED_MUTUAL_RECURSION
#define INCLUDED_MUTUAL_RECURSION

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct MutualRecursion {
  static bool is_even(const unsigned int &n);
  static bool is_odd(const unsigned int &n);
  template <typename t_A> struct tree;
  template <typename t_A> struct forest;

  template <typename t_A> struct tree {
    // TYPES
    struct Leaf {
      t_A d_a0;
    };

    struct Node {
      std::unique_ptr<forest<t_A>> d_a0;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Leaf _v) : d_v_(std::move(_v)) {}

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
    tree<t_A> clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Leaf>(_sv.v())) {
        const auto &[d_a0] = std::get<Leaf>(_sv.v());
        return tree<t_A>(Leaf{d_a0});
      } else {
        const auto &[d_a0] = std::get<Node>(_sv.v());
        return tree<t_A>(Node{
            d_a0 ? std::make_unique<MutualRecursion::forest<t_A>>(d_a0->clone())
                 : nullptr});
      }
    }

    // CREATORS
    template <typename _U> explicit tree(const tree<_U> &_other) {
      if (std::holds_alternative<typename tree<_U>::Leaf>(_other.v())) {
        const auto &[d_a0] = std::get<typename tree<_U>::Leaf>(_other.v());
        d_v_ = Leaf{t_A(d_a0)};
      } else {
        const auto &[d_a0] = std::get<typename tree<_U>::Node>(_other.v());
        d_v_ = Node{d_a0 ? std::make_unique<MutualRecursion::forest<t_A>>(*d_a0)
                         : nullptr};
      }
    }

    static tree<t_A> leaf(t_A a0) { return tree(Leaf{std::move(a0)}); }

    static tree<t_A> node(forest<t_A> a0) {
      return tree(Node{std::make_unique<forest<t_A>>(std::move(a0))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
  };

  template <typename t_A> struct forest {
    // TYPES
    struct Empty {};

    struct Trees {
      std::unique_ptr<tree<t_A>> d_a0;
      std::unique_ptr<forest<t_A>> d_a1;
    };

    using variant_t = std::variant<Empty, Trees>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    forest() {}

    explicit forest(Empty _v) : d_v_(_v) {}

    explicit forest(Trees _v) : d_v_(std::move(_v)) {}

    forest(const forest<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    forest(forest<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    forest<t_A> &operator=(const forest<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    forest<t_A> &operator=(forest<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    forest clone() const {
      forest _out{};

      struct _CloneFrame {
        const forest *_src;
        forest *_dst;
      };

      std::vector<_CloneFrame> _stack;
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const forest *_src = _frame._src;
        forest *_dst = _frame._dst;
        if (std::holds_alternative<Empty>(_src->v())) {
          const auto &_alt = std::get<Empty>(_src->v());
          _dst->d_v_ = Empty{};
        } else {
          const auto &_alt = std::get<Trees>(_src->v());
          _dst->d_v_ =
              Trees{_alt.d_a0 ? std::make_unique<MutualRecursion::tree<t_A>>(
                                    _alt.d_a0->clone())
                              : nullptr,
                    _alt.d_a1 ? std::make_unique<forest>() : nullptr};
          auto &_dst_alt = std::get<Trees>(_dst->d_v_);
          if (_alt.d_a1)
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        }
      }
      return _out;
    }

    // CREATORS
    template <typename _U> explicit forest(const forest<_U> &_other) {
      if (std::holds_alternative<typename forest<_U>::Empty>(_other.v())) {
        d_v_ = Empty{};
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename forest<_U>::Trees>(_other.v());
        d_v_ = Trees{d_a0 ? std::make_unique<MutualRecursion::tree<t_A>>(*d_a0)
                          : nullptr,
                     d_a1 ? std::make_unique<forest<t_A>>(*d_a1) : nullptr};
      }
    }

    static forest<t_A> empty() { return forest(Empty{}); }

    static forest<t_A> trees(tree<t_A> a0, forest<t_A> a1) {
      return forest(Trees{std::make_unique<tree<t_A>>(std::move(a0)),
                          std::make_unique<forest<t_A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~forest() {
      std::vector<std::unique_ptr<forest>> _stack;
      auto _drain = [&](forest &_node) {
        if (std::holds_alternative<Trees>(_node.d_v_)) {
          auto &_alt = std::get<Trees>(_node.d_v_);
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
    const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, MapsTo<T2, T1> F0,
            MapsTo<T2, forest<T1>> F1>
  static T2 tree_rect(F0 &&f, F1 &&f0, const tree<T1> &t) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
      const auto &[d_a0] = std::get<typename tree<T1>::Leaf>(t.v());
      return f(d_a0);
    } else {
      const auto &[d_a0] = std::get<typename tree<T1>::Node>(t.v());
      return f0(*(d_a0));
    }
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0,
            MapsTo<T2, forest<T1>> F1>
  static T2 tree_rec(F0 &&f, F1 &&f0, const tree<T1> &t) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
      const auto &[d_a0] = std::get<typename tree<T1>::Leaf>(t.v());
      return f(d_a0);
    } else {
      const auto &[d_a0] = std::get<typename tree<T1>::Node>(t.v());
      return f0(*(d_a0));
    }
  }

  template <typename T1, typename T2, MapsTo<T2, tree<T1>, forest<T1>, T2> F1>
  static T2 forest_rect(const T2 f, F1 &&f0, const forest<T1> &f1) {
    if (std::holds_alternative<typename forest<T1>::Empty>(f1.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename forest<T1>::Trees>(f1.v());
      return f0(*(d_a0), *(d_a1), forest_rect<T1, T2>(f, f0, *(d_a1)));
    }
  }

  template <typename T1, typename T2, MapsTo<T2, tree<T1>, forest<T1>, T2> F1>
  static T2 forest_rec(const T2 f, F1 &&f0, const forest<T1> &f1) {
    if (std::holds_alternative<typename forest<T1>::Empty>(f1.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename forest<T1>::Trees>(f1.v());
      return f0(*(d_a0), *(d_a1), forest_rec<T1, T2>(f, f0, *(d_a1)));
    }
  }

  template <typename T1> static unsigned int tree_size(const tree<T1> &t) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
      return 1u;
    } else {
      const auto &[d_a0] = std::get<typename tree<T1>::Node>(t.v());
      return forest_size<T1>(*(d_a0));
    }
  }

  template <typename T1> static unsigned int forest_size(const forest<T1> &f) {
    if (std::holds_alternative<typename forest<T1>::Empty>(f.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename forest<T1>::Trees>(f.v());
      return (tree_size<T1>(*(d_a0)) + forest_size<T1>(*(d_a1)));
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
