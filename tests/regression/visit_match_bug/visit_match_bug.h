#ifndef INCLUDED_VISIT_MATCH_BUG
#define INCLUDED_VISIT_MATCH_BUG

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_unique<T>(x->clone()) : nullptr;
  } else {
    return x ? std::make_unique<T>(*x) : nullptr;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using T = std::remove_cvref_t<Target>;
  using S = std::remove_cvref_t<Source>;
  if constexpr (requires(const S &s) {
                  s.has_value();
                  *s;
                }) {
    if (!x.has_value())
      return T{};
    using TInner = std::remove_cvref_t<decltype(*std::declval<const T &>())>;
    return T{clone_as_value<TInner>(*x)};
  } else if constexpr (std::is_same_v<T, S>) {
    if constexpr (is_unique_ptr<T>::value) {
      return clone_value(x);
    } else if constexpr (requires { x.clone(); }) {
      return x.clone();
    } else {
      return x;
    }
  } else if constexpr (is_unique_ptr<S>::value) {
    if (!x)
      return T{};
    return clone_as_value<T>(*x);
  } else if constexpr (is_unique_ptr<T>::value) {
    using Inner = typename is_unique_ptr<T>::element_type;
    return std::make_unique<Inner>(clone_as_value<Inner>(x));
  } else {
    return T(x);
  }
}

struct VisitMatchBug {
  struct Tree {
    // TYPES
    struct Leaf {
      unsigned int d_a0;
    };

    struct Node {
      std::unique_ptr<Tree> d_a0;
      unsigned int d_a1;
      std::unique_ptr<Tree> d_a2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    Tree() {}

    explicit Tree(Leaf _v) : d_v_(std::move(_v)) {}

    explicit Tree(Node _v) : d_v_(std::move(_v)) {}

    Tree(const Tree &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    Tree(Tree &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) Tree &operator=(const Tree &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) Tree &operator=(Tree &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) Tree clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Leaf>(_sv.v())) {
        const auto &[d_a0] = std::get<Leaf>(_sv.v());
        return Tree(Leaf{d_a0});
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<Node>(_sv.v());
        return Tree(Node{clone_value(d_a0), d_a1, clone_value(d_a2)});
      }
    }

    // CREATORS
    __attribute__((pure)) static Tree leaf(unsigned int a0) {
      return Tree(Leaf{std::move(a0)});
    }

    __attribute__((pure)) static Tree node(const Tree &a0, unsigned int a1,
                                           const Tree &a2) {
      return Tree(Node{std::make_unique<Tree>(a0), std::move(a1),
                       std::make_unique<Tree>(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) Tree *operator->() { return this; }

    __attribute__((pure)) const Tree *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = Tree(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, Tree, T1, unsigned int, Tree, T1> F1>
  static T1 Tree_rect(F0 &&f, F1 &&f0, const Tree &t) {
    if (std::holds_alternative<typename Tree::Leaf>(t.v())) {
      const auto &[d_a0] = std::get<typename Tree::Leaf>(t.v());
      return f(d_a0);
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename Tree::Node>(t.v());
      return f0(*(d_a0), Tree_rect<T1>(f, f0, *(d_a0)), d_a1, *(d_a2),
                Tree_rect<T1>(f, f0, *(d_a2)));
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, Tree, T1, unsigned int, Tree, T1> F1>
  static T1 Tree_rec(F0 &&f, F1 &&f0, const Tree &t) {
    if (std::holds_alternative<typename Tree::Leaf>(t.v())) {
      const auto &[d_a0] = std::get<typename Tree::Leaf>(t.v());
      return f(d_a0);
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename Tree::Node>(t.v());
      return f0(*(d_a0), Tree_rec<T1>(f, f0, *(d_a0)), d_a1, *(d_a2),
                Tree_rec<T1>(f, f0, *(d_a2)));
    }
  }

  __attribute__((pure)) static Tree consume(Tree t);
  __attribute__((pure)) static unsigned int match_after_consume(const Tree &t);
  __attribute__((pure)) static unsigned int match_last_use(const Tree &t);
  __attribute__((pure)) static unsigned int nested_match_consume(const Tree &t);
  __attribute__((pure)) static unsigned int chain_then_match(const Tree &t1);

  struct State {
    unsigned int value;
    unsigned int data;

    __attribute__((pure)) State *operator->() { return this; }

    __attribute__((pure)) const State *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) State clone() const {
      return State{(*(this)).value, (*(this)).data};
    }
  };

  __attribute__((pure)) static unsigned int match_extract_field(const State &s);
  __attribute__((pure)) static unsigned int match_extract_two(const State &s);
  __attribute__((pure)) static unsigned int match_nested(const State &s);
  __attribute__((pure)) static unsigned int match_in_tail(const State &s);
  __attribute__((pure)) static unsigned int match_in_expr(const State &s);
};

#endif // INCLUDED_VISIT_MATCH_BUG
