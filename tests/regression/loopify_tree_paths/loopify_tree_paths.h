#ifndef INCLUDED_LOOPIFY_TREE_PATHS
#define INCLUDED_LOOPIFY_TREE_PATHS

#include <algorithm>
#include <any>
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
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  List<A> app(List<A> m) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return m;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return List<A>::cons(a0, a1->app(std::move(m)));
    }
  }
};

struct LoopifyTreePaths {
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<tree> a0;
      uint64_t a1;
      std::shared_ptr<tree> a2;
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

    static tree leaf() { return tree(Leaf{}); }

    static tree node(tree a0, uint64_t a1, tree a2) {
      return tree(Node{std::make_shared<tree>(std::move(a0)), a1,
                       std::make_shared<tree>(std::move(a2))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    List<uint64_t> flatten_paths() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return List<uint64_t>::nil();
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return List<uint64_t>::cons(
            a1, a0->flatten_paths().app(a2->flatten_paths()));
      }
    }

    uint64_t max_path_sum() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return (a1 + std::max(a0->max_path_sum(), a2->max_path_sum()));
      }
    }

    std::optional<List<uint64_t>> find_path_sum(uint64_t acc,
                                                uint64_t target) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        if (acc == target) {
          return std::make_optional<List<uint64_t>>(List<uint64_t>::nil());
        } else {
          return std::optional<List<uint64_t>>();
        }
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        uint64_t new_acc = (acc + a1);
        auto _cs = a0->find_path_sum(new_acc, target);
        if (_cs.has_value()) {
          const List<uint64_t> &path = *_cs;
          return std::make_optional<List<uint64_t>>(
              List<uint64_t>::cons(a1, path));
        } else {
          auto _cs1 = a2->find_path_sum(new_acc, target);
          if (_cs1.has_value()) {
            const List<uint64_t> &path = *_cs1;
            return std::make_optional<List<uint64_t>>(
                List<uint64_t>::cons(a1, path));
          } else {
            return std::optional<List<uint64_t>>();
          }
        }
      }
    }

    uint64_t count_paths_sum(uint64_t target) const {
      return this->count_paths_sum_aux(UINT64_C(0), target);
    }

    uint64_t count_paths_sum_aux(uint64_t acc, uint64_t target) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        if (acc == target) {
          return UINT64_C(1);
        } else {
          return UINT64_C(0);
        }
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        uint64_t new_acc = (acc + a1);
        return (a0->count_paths_sum_aux(new_acc, target) +
                a2->count_paths_sum_aux(new_acc, target));
      }
    }

    List<List<uint64_t>> paths() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return List<List<uint64_t>>::cons(List<uint64_t>::nil(),
                                          List<List<uint64_t>>::nil());
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return map_cons(a1, a0->paths()).app(map_cons(a1, a2->paths()));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, uint64_t &, tree &,
                                     T1 &>
    T1 tree_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return f0(*a0, a0->template tree_rec<T1>(f, f0), a1, *a2,
                  a2->template tree_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, uint64_t &, tree &,
                                     T1 &>
    T1 tree_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return f0(*a0, a0->template tree_rect<T1>(f, f0), a1, *a2,
                  a2->template tree_rect<T1>(f, f0));
      }
    }
  };

  static List<List<uint64_t>> map_cons(uint64_t x,
                                       const List<List<uint64_t>> &ll);

  struct bool_tree {
    // TYPES
    struct BLeaf {
      uint64_t a0;
    };

    struct BNode {
      std::shared_ptr<bool_tree> a0;
      std::shared_ptr<bool_tree> a1;
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

    static bool_tree bleaf(uint64_t a0) { return bool_tree(BLeaf{a0}); }

    static bool_tree bnode(bool_tree a0, bool_tree a1) {
      return bool_tree(BNode{std::make_shared<bool_tree>(std::move(a0)),
                             std::make_shared<bool_tree>(std::move(a1))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename F0>
      requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
    bool and_search(F0 &&p) const {
      if (std::holds_alternative<typename bool_tree::BLeaf>(this->v())) {
        const auto &[a0] = std::get<typename bool_tree::BLeaf>(this->v());
        return p(a0);
      } else {
        const auto &[a0, a1] = std::get<typename bool_tree::BNode>(this->v());
        return (a0->and_search(p) && a1->and_search(p));
      }
    }

    template <typename F0>
      requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
    bool or_search(F0 &&p) const {
      if (std::holds_alternative<typename bool_tree::BLeaf>(this->v())) {
        const auto &[a0] = std::get<typename bool_tree::BLeaf>(this->v());
        return p(a0);
      } else {
        const auto &[a0, a1] = std::get<typename bool_tree::BNode>(this->v());
        return (a0->or_search(p) || a1->or_search(p));
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, bool_tree &, T1 &, bool_tree &,
                                     T1 &>
    T1 bool_tree_rec(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename bool_tree::BLeaf>(this->v())) {
        const auto &[a0] = std::get<typename bool_tree::BLeaf>(this->v());
        return f(a0);
      } else {
        const auto &[a0, a1] = std::get<typename bool_tree::BNode>(this->v());
        return f0(*a0, a0->template bool_tree_rec<T1>(f, f0), *a1,
                  a1->template bool_tree_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, bool_tree &, T1 &, bool_tree &,
                                     T1 &>
    T1 bool_tree_rect(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename bool_tree::BLeaf>(this->v())) {
        const auto &[a0] = std::get<typename bool_tree::BLeaf>(this->v());
        return f(a0);
      } else {
        const auto &[a0, a1] = std::get<typename bool_tree::BNode>(this->v());
        return f0(*a0, a0->template bool_tree_rect<T1>(f, f0), *a1,
                  a1->template bool_tree_rect<T1>(f, f0));
      }
    }
  };
};

#endif // INCLUDED_LOOPIFY_TREE_PATHS
