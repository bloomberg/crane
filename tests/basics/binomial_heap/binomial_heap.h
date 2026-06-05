#ifndef INCLUDED_BINOMIAL_HEAP
#define INCLUDED_BINOMIAL_HEAP

#include <any>
#include <functional>
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
    A a;
    std::shared_ptr<List<A>> l;
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

  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        _drain(_cur->v_mut());
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct BinomialHeap {
  using key = uint64_t;

  struct tree {
    // TYPES
    struct Node {
      key a0;
      std::shared_ptr<tree> a1;
      std::shared_ptr<tree> a2;
    };

    struct Leaf {};

    using variant_t = std::variant<Node, Leaf>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Node _v) : v_(std::move(_v)) {}

    explicit tree(Leaf _v) : v_(_v) {}

    static tree node(key a0, tree a1, tree a2) {
      return tree(Node{std::move(a0), std::make_shared<tree>(std::move(a1)),
                       std::make_shared<tree>(std::move(a2))});
    }

    static tree leaf() { return tree(Leaf{}); }

    // MANIPULATORS
    ~tree() {
      std::vector<std::shared_ptr<tree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
          if (_alt->a2) {
            _stack.push_back(std::move(_alt->a2));
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          _drain(_cur->v_mut());
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, tree &, T1 &, tree &,
                                   T1 &>
  static T1 tree_rect(F0 &&f, T1 f0, const tree &t) {
    if (std::holds_alternative<typename tree::Node>(t.v())) {
      const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
      return f(a0, *a1, tree_rect<T1>(f, f0, *a1), *a2,
               tree_rect<T1>(f, f0, *a2));
    } else {
      return f0;
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, tree &, T1 &, tree &,
                                   T1 &>
  static T1 tree_rec(F0 &&f, T1 f0, const tree &t) {
    if (std::holds_alternative<typename tree::Node>(t.v())) {
      const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
      return f(a0, *a1, tree_rec<T1>(f, f0, *a1), *a2,
               tree_rec<T1>(f, f0, *a2));
    } else {
      return f0;
    }
  }

  using priqueue = List<tree>;
  static inline const priqueue empty = List<tree>::nil();
  static tree smash(const tree &t, const tree &u);
  static List<tree> carry(const List<tree> &q, tree t);
  static priqueue insert(uint64_t x, const List<tree> &q);
  static priqueue join(const List<tree> &p, const List<tree> &q, tree c);

  static priqueue unzip(const tree &t,
                        std::function<List<tree>(List<tree>)> cont) {
    if (std::holds_alternative<typename tree::Node>(t.v())) {
      const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
      const tree &a1_value = *a1;
      const tree &a2_value = *a2;
      std::function<List<tree>(List<tree>)> f =
          [=](const List<tree> &q) mutable {
            return List<tree>::cons(tree::node(a0, a1_value, tree::leaf()),
                                    cont(q));
          };
      return unzip(a2_value, f);
    } else {
      return cont(List<tree>::nil());
    }
  }

  static priqueue heap_delete_max(const tree &t);
  static key find_max_helper(uint64_t current, const List<tree> &q);
  static std::optional<key> find_max(const List<tree> &q);
  static std::pair<priqueue, priqueue> delete_max_aux(uint64_t m,
                                                      const List<tree> &p);
  static std::optional<std::pair<key, priqueue>>
  delete_max(const List<tree> &q);
  static priqueue merge(const List<tree> &p, const List<tree> &q);
  static priqueue insert_list(const List<uint64_t> &l, List<tree> q);
  static List<uint64_t> make_list(uint64_t n, List<uint64_t> l);
  static key help(const List<tree> &c);
  static inline const key example1 = help(merge(
      insert(UINT64_C(5),
             insert(UINT64_C(3), insert(UINT64_C(7), List<tree>::nil()))),
      insert(UINT64_C(3),
             insert(UINT64_C(6), insert(UINT64_C(9), List<tree>::nil())))));
  static inline const key example2 =
      help(merge(insert_list(make_list(UINT64_C(10), List<uint64_t>::nil()),
                             List<tree>::nil()),
                 insert_list(make_list(UINT64_C(11), List<uint64_t>::nil()),
                             List<tree>::nil())));
};

#endif // INCLUDED_BINOMIAL_HEAP
