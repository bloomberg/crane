#ifndef INCLUDED_MUTUAL_RECURSION
#define INCLUDED_MUTUAL_RECURSION

#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MutualRecursion {
  static bool is_even(uint64_t n);
  static bool is_odd(uint64_t n);
  template <typename A> struct tree;
  template <typename A> struct forest;

  template <typename A> struct tree {
    // TYPES
    struct Leaf {
      A a0;
    };

    struct Node {
      std::shared_ptr<forest<A>> a0;
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

    template <typename _U> explicit tree(const tree<_U> &_other) {
      if (std::holds_alternative<typename tree<_U>::Leaf>(_other.v())) {
        const auto &[a0] = std::get<typename tree<_U>::Leaf>(_other.v());
        this->v_ = Leaf{[&]() -> A {
          if constexpr (std::is_same_v<_U, std::any>) {
            if (a0.type() == typeid(A))
              return std::any_cast<A>(a0);
            if constexpr (requires {
                            typename A::first_type;
                            typename A::second_type;
                          }) {
              const auto &[_k, _v] =
                  std::any_cast<std::pair<std::any, std::any>>(a0);
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
            return std::any_cast<A>(a0);
          } else
            return A(a0);
        }()};
      } else {
        const auto &[a0] = std::get<typename tree<_U>::Node>(_other.v());
        this->v_ = Node{a0 ? std::make_shared<MutualRecursion::forest<A>>(*a0)
                           : nullptr};
      }
    }

    static tree<A> leaf(A a0) { return tree(Leaf{std::move(a0)}); }

    static tree<A> node(forest<A> a0) {
      return tree(Node{std::make_shared<forest<A>>(std::move(a0))});
    }

    // MANIPULATORS
    ~tree() {
      std::vector<std::any> _stack = {};
      auto _drain_self = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
        }
      };
      _drain_self(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (auto *_sp = std::any_cast<std::shared_ptr<tree<A>>>(&_cur)) {
          if (*_sp && (*_sp).use_count() == 1) {
            _drain_self((*_sp)->v_mut());
          }
        } else {
          if (auto *_sp = std::any_cast<std::shared_ptr<forest<A>>>(&_cur)) {
            if (*_sp && (*_sp).use_count() == 1) {
              auto &_pv = (*_sp)->v_mut();
              if (auto *_alt = std::get_if<typename forest<A>::Trees>(&_pv)) {
                if (_alt->a0) {
                  _stack.push_back(std::move(_alt->a0));
                }
                if (_alt->a1) {
                  _stack.push_back(std::move(_alt->a1));
                }
              }
            }
          }
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
      std::shared_ptr<tree<A>> a0;
      std::shared_ptr<forest<A>> a1;
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

    template <typename _U> explicit forest(const forest<_U> &_other) {
      if (std::holds_alternative<typename forest<_U>::Empty>(_other.v())) {
        this->v_ = Empty{};
      } else {
        const auto &[a0, a1] = std::get<typename forest<_U>::Trees>(_other.v());
        this->v_ = Trees{a0 ? std::make_shared<MutualRecursion::tree<A>>(*a0)
                            : nullptr,
                         a1 ? std::make_shared<forest<A>>(*a1) : nullptr};
      }
    }

    static forest<A> empty() { return forest(Empty{}); }

    static forest<A> trees(tree<A> a0, forest<A> a1) {
      return forest(Trees{std::make_shared<tree<A>>(std::move(a0)),
                          std::make_shared<forest<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~forest() {
      std::vector<std::any> _stack = {};
      auto _drain_self = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Trees>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
      };
      _drain_self(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (auto *_sp = std::any_cast<std::shared_ptr<forest<A>>>(&_cur)) {
          if (*_sp && (*_sp).use_count() == 1) {
            _drain_self((*_sp)->v_mut());
          }
        } else {
          if (auto *_sp = std::any_cast<std::shared_ptr<tree<A>>>(&_cur)) {
            if (*_sp && (*_sp).use_count() == 1) {
              auto &_pv = (*_sp)->v_mut();
              if (auto *_alt = std::get_if<typename tree<A>::Node>(&_pv)) {
                if (_alt->a0) {
                  _stack.push_back(std::move(_alt->a0));
                }
              }
            }
          }
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

  template <typename T1> static uint64_t tree_size(const tree<T1> &t) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
      return UINT64_C(1);
    } else {
      const auto &[a0] = std::get<typename tree<T1>::Node>(t.v());
      return forest_size<T1>(*a0);
    }
  }

  template <typename T1> static uint64_t forest_size(const forest<T1> &f) {
    if (std::holds_alternative<typename forest<T1>::Empty>(f.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename forest<T1>::Trees>(f.v());
      return (tree_size<T1>(*a0) + forest_size<T1>(*a1));
    }
  }

  static uint64_t tree_sum(const tree<uint64_t> &t);
  static uint64_t forest_sum(const forest<uint64_t> &f);
  static inline const bool test_even_0 = is_even(UINT64_C(0));
  static inline const bool test_even_4 = is_even(UINT64_C(4));
  static inline const bool test_odd_3 = is_odd(UINT64_C(3));
  static inline const bool test_odd_4 = is_odd(UINT64_C(4));
  static inline const tree<uint64_t> simple_tree =
      tree<uint64_t>::node(forest<uint64_t>::trees(
          tree<uint64_t>::leaf(UINT64_C(1)),
          forest<uint64_t>::trees(tree<uint64_t>::leaf(UINT64_C(2)),
                                  forest<uint64_t>::empty())));
  static inline const tree<uint64_t> nested_tree =
      tree<uint64_t>::node(forest<uint64_t>::trees(
          tree<uint64_t>::node(forest<uint64_t>::trees(
              tree<uint64_t>::leaf(UINT64_C(3)), forest<uint64_t>::empty())),
          forest<uint64_t>::trees(tree<uint64_t>::leaf(UINT64_C(4)),
                                  forest<uint64_t>::empty())));
  static inline const uint64_t test_size_simple =
      tree_size<uint64_t>(simple_tree);
  static inline const uint64_t test_size_nested =
      tree_size<uint64_t>(nested_tree);
  static inline const uint64_t test_sum_simple = tree_sum(simple_tree);
  static inline const uint64_t test_sum_nested = tree_sum(nested_tree);
};

#endif // INCLUDED_MUTUAL_RECURSION
