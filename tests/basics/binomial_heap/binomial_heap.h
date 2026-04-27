#ifndef INCLUDED_BINOMIAL_HEAP
#define INCLUDED_BINOMIAL_HEAP

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

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
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) List<t_A> *operator->() { return this; }

  __attribute__((pure)) const List<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = List<t_A>(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct BinomialHeap {
  using key = unsigned int;

  struct tree {
    // TYPES
    struct Node {
      key d_a0;
      std::unique_ptr<tree> d_a1;
      std::unique_ptr<tree> d_a2;
    };

    struct Leaf {};

    using variant_t = std::variant<Node, Leaf>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Node _v) : d_v_(std::move(_v)) {}

    explicit tree(Leaf _v) : d_v_(_v) {}

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
      if (std::holds_alternative<Node>(_sv.v())) {
        const auto &[d_a0, d_a1, d_a2] = std::get<Node>(_sv.v());
        return tree(
            Node{d_a0,
                 d_a1 ? std::make_unique<BinomialHeap::tree>(d_a1->clone())
                      : nullptr,
                 d_a2 ? std::make_unique<BinomialHeap::tree>(d_a2->clone())
                      : nullptr});
      } else {
        return tree(Leaf{});
      }
    }

    // CREATORS
    __attribute__((pure)) static tree node(key a0, const tree &a1,
                                           const tree &a2) {
      return tree(Node{std::move(a0), std::make_unique<tree>(a1),
                       std::make_unique<tree>(a2)});
    }

    __attribute__((pure)) static tree leaf() { return tree(Leaf{}); }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) tree *operator->() { return this; }

    __attribute__((pure)) const tree *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = tree(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int, tree, T1, tree, T1> F0>
  static T1 tree_rect(F0 &&f, const T1 f0, const tree &t) {
    if (std::holds_alternative<typename tree::Node>(t.v())) {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(t.v());
      return f(d_a0, *(d_a1), tree_rect<T1>(f, f0, *(d_a1)), *(d_a2),
               tree_rect<T1>(f, f0, *(d_a2)));
    } else {
      return f0;
    }
  }

  template <typename T1, MapsTo<T1, unsigned int, tree, T1, tree, T1> F0>
  static T1 tree_rec(F0 &&f, const T1 f0, const tree &t) {
    if (std::holds_alternative<typename tree::Node>(t.v())) {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(t.v());
      return f(d_a0, *(d_a1), tree_rec<T1>(f, f0, *(d_a1)), *(d_a2),
               tree_rec<T1>(f, f0, *(d_a2)));
    } else {
      return f0;
    }
  }

  using priqueue = List<tree>;
  static inline const priqueue empty = List<tree>::nil();
  __attribute__((pure)) static tree smash(const tree &t, const tree &u);
  __attribute__((pure)) static List<tree> carry(const List<tree> &q, tree t);
  __attribute__((pure)) static priqueue insert(unsigned int x,
                                               const List<tree> &q);
  __attribute__((pure)) static priqueue join(const List<tree> &p,
                                             const List<tree> &q, tree c);

  __attribute__((pure)) static priqueue
  unzip(const tree &t, const std::function<List<tree>(List<tree>)> cont) {
    if (std::holds_alternative<typename tree::Node>(t.v())) {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(t.v());
      tree d_a1_value = *(d_a1);
      tree d_a2_value = *(d_a2);
      std::function<List<tree>(List<tree>)> f =
          [=](const List<tree> &q) mutable {
            return List<tree>::cons(tree::node(d_a0, d_a1_value, tree::leaf()),
                                    cont(q));
          };
      return unzip(d_a2_value, f);
    } else {
      return cont(List<tree>::nil());
    }
  }

  __attribute__((pure)) static priqueue heap_delete_max(const tree &t);
  __attribute__((pure)) static key find_max_helper(unsigned int current,
                                                   const List<tree> &q);
  __attribute__((pure)) static std::optional<key> find_max(const List<tree> &q);
  __attribute__((pure)) static std::pair<priqueue, priqueue>
  delete_max_aux(const unsigned int &m, const List<tree> &p);
  __attribute__((pure)) static std::optional<std::pair<key, priqueue>>
  delete_max(const List<tree> &q);
  __attribute__((pure)) static priqueue merge(const List<tree> &p,
                                              const List<tree> &q);
  __attribute__((pure)) static priqueue insert_list(const List<unsigned int> &l,
                                                    List<tree> q);
  __attribute__((pure)) static List<unsigned int>
  make_list(const unsigned int &n, List<unsigned int> l);
  __attribute__((pure)) static key help(const List<tree> &c);
  static inline const key example1 =
      help(merge(insert(5u, insert(3u, insert(7u, List<tree>::nil()))),
                 insert(3u, insert(6u, insert(9u, List<tree>::nil())))));
  static inline const key example2 = help(merge(
      insert_list(make_list(10u, List<unsigned int>::nil()), List<tree>::nil()),
      insert_list(make_list(11u, List<unsigned int>::nil()),
                  List<tree>::nil())));
};

#endif // INCLUDED_BINOMIAL_HEAP
