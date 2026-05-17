#ifndef INCLUDED_DEEP_MAP
#define INCLUDED_DEEP_MAP

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct DeepMap {
  template <typename A> struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::unique_ptr<tree<A>> a0;
      A a1;
      std::unique_ptr<tree<A>> a2;
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

    tree(const tree<A> &_other) : v_(std::move(_other.clone().v_)) {}

    tree(tree<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

    tree<A> &operator=(const tree<A> &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    tree<A> &operator=(tree<A> &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    tree<A> clone() const {
      tree<A> _out{};

      struct _CloneFrame {
        const tree<A> *_src;
        tree<A> *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const tree<A> *_src = _frame._src;
        tree<A> *_dst = _frame._dst;
        if (std::holds_alternative<Leaf>(_src->v())) {
          _dst->v_ = Leaf{};
        } else {
          const auto &_alt = std::get<Node>(_src->v());
          _dst->v_ =
              Node{_alt.a0 ? std::make_unique<tree<A>>() : nullptr, _alt.a1,
                   _alt.a2 ? std::make_unique<tree<A>>() : nullptr};
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
    template <typename _U> explicit tree(const tree<_U> &_other) {
      if (std::holds_alternative<typename tree<_U>::Leaf>(_other.v())) {
        this->v_ = Leaf{};
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename tree<_U>::Node>(_other.v());
        this->v_ = Node{a0 ? std::make_unique<tree<A>>(*a0) : nullptr, A(a1),
                        a2 ? std::make_unique<tree<A>>(*a2) : nullptr};
      }
    }

    static tree<A> leaf() { return tree(Leaf{}); }

    static tree<A> node(tree<A> a0, A a1, tree<A> a2) {
      return tree(Node{std::make_unique<tree<A>>(std::move(a0)), std::move(a1),
                       std::make_unique<tree<A>>(std::move(a2))});
    }

    // MANIPULATORS
    ~tree() {
      std::vector<std::unique_ptr<tree<A>>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](tree<A> &_node) {
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
  };

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, tree<T1> &, T2 &, T1 &, tree<T1> &,
                                   T2 &>
  static T2 tree_rect(T2 f, F1 &&f0, const tree<T1> &t) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[a0, a1, a2] = std::get<typename tree<T1>::Node>(t.v());
      return f0(*a0, tree_rect<T1, T2>(f, f0, *a0), a1, *a2,
                tree_rect<T1, T2>(f, f0, *a2));
    }
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, tree<T1> &, T2 &, T1 &, tree<T1> &,
                                   T2 &>
  static T2 tree_rec(T2 f, F1 &&f0, const tree<T1> &t) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[a0, a1, a2] = std::get<typename tree<T1>::Node>(t.v());
      return f0(*a0, tree_rec<T1, T2>(f, f0, *a0), a1, *a2,
                tree_rec<T1, T2>(f, f0, *a2));
    }
  }

  /// Build a maximally-unbalanced tree (right spine = linked list).
  /// Tail-recursive via accumulator, should be loopified.
  static tree<unsigned int> build_right(unsigned int n, tree<unsigned int> acc);

  /// Recursive tree map — visits every node.
  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static tree<T2> tmap(F0 &&f, const tree<T1> &t) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
      return tree<T2>::leaf();
    } else {
      const auto &[a0, a1, a2] = std::get<typename tree<T1>::Node>(t.v());
      return tree<T2>::node(tmap<T1, T2>(f, *a0), f(a1), tmap<T1, T2>(f, *a2));
    }
  }

  static tree<unsigned int> map_inc(const tree<unsigned int> &t);
  /// Get root value.
  static unsigned int root_or_zero(const tree<unsigned int> &t);
};

#endif // INCLUDED_DEEP_MAP
