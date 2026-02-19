#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct NestedInductive {
  template <typename A> struct list {
  public:
    struct nil {};
    struct cons {
      A _a0;
      std::shared_ptr<list<A>> _a1;
    };
    using variant_t = std::variant<nil, cons>;

  private:
    variant_t v_;
    explicit list(nil _v) : v_(std::move(_v)) {}
    explicit list(cons _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<list<A>> nil_() {
        return std::shared_ptr<list<A>>(new list<A>(nil{}));
      }
      static std::shared_ptr<list<A>>
      cons_(A a0, const std::shared_ptr<list<A>> &a1) {
        return std::shared_ptr<list<A>>(new list<A>(cons{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<list<T1>>, T2> F1>
  static T2 list_rect(const T2 f, F1 &&f0, const std::shared_ptr<list<T1>> &l) {
    return std::visit(
        Overloaded{[&](const typename list<T1>::nil _args) -> T2 { return f; },
                   [&](const typename list<T1>::cons _args) -> T2 {
                     T1 y = _args._a0;
                     std::shared_ptr<list<T1>> l0 = _args._a1;
                     return f0(y, l0, list_rect<T1, T2>(f, f0, l0));
                   }},
        l->v());
  }

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<list<T1>>, T2> F1>
  static T2 list_rec(const T2 f, F1 &&f0, const std::shared_ptr<list<T1>> &l) {
    return std::visit(
        Overloaded{[&](const typename list<T1>::nil _args) -> T2 { return f; },
                   [&](const typename list<T1>::cons _args) -> T2 {
                     T1 y = _args._a0;
                     std::shared_ptr<list<T1>> l0 = _args._a1;
                     return f0(y, l0, list_rec<T1, T2>(f, f0, l0));
                   }},
        l->v());
  }

  template <typename A> struct rose {
  public:
    struct Node {
      A _a0;
      std::shared_ptr<list<std::shared_ptr<rose<A>>>> _a1;
    };
    using variant_t = std::variant<Node>;

  private:
    variant_t v_;
    explicit rose(Node _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<rose<A>>
      Node_(A a0, const std::shared_ptr<list<std::shared_ptr<rose<A>>>> &a1) {
        return std::shared_ptr<rose<A>>(new rose<A>(Node{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<list<std::shared_ptr<rose<T1>>>>> F0>
  static T2 rose_rect(F0 &&f, const std::shared_ptr<rose<T1>> &r) {
    return std::visit(
        Overloaded{[&](const typename rose<T1>::Node _args) -> T2 {
          T1 a = _args._a0;
          std::shared_ptr<list<std::shared_ptr<rose<T1>>>> l = _args._a1;
          return f(a, l);
        }},
        r->v());
  }

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<list<std::shared_ptr<rose<T1>>>>> F0>
  static T2 rose_rec(F0 &&f, const std::shared_ptr<rose<T1>> &r) {
    return std::visit(
        Overloaded{[&](const typename rose<T1>::Node _args) -> T2 {
          T1 a = _args._a0;
          std::shared_ptr<list<std::shared_ptr<rose<T1>>>> l = _args._a1;
          return f(a, l);
        }},
        r->v());
  }

  template <typename T1> static T1 root(const std::shared_ptr<rose<T1>> &t) {
    return std::visit(Overloaded{[](const typename rose<T1>::Node _args) -> T1 {
                        T1 x = _args._a0;
                        return x;
                      }},
                      t->v());
  }

  template <typename T1>
  static unsigned int list_length(const std::shared_ptr<list<T1>> &l) {
    return std::visit(
        Overloaded{[](const typename list<T1>::nil _args) -> unsigned int {
                     return 0u;
                   },
                   [](const typename list<T1>::cons _args) -> unsigned int {
                     std::shared_ptr<list<T1>> rest = _args._a1;
                     return (1u + list_length<T1>(rest));
                   }},
        l->v());
  }

  template <typename T1>
  static unsigned int children_count(const std::shared_ptr<rose<T1>> &t) {
    return std::visit(
        Overloaded{[](const typename rose<T1>::Node _args) -> unsigned int {
          std::shared_ptr<list<std::shared_ptr<rose<T1>>>> children = _args._a1;
          return list_length<std::shared_ptr<rose<T1>>>(children);
        }},
        t->v());
  }

  static std::shared_ptr<rose<unsigned int>> leaf(const unsigned int n);

  static inline const std::shared_ptr<rose<unsigned int>> small_tree =
      rose<unsigned int>::ctor::Node_(
          1u,
          list<std::shared_ptr<rose<unsigned int>>>::ctor::cons_(
              leaf(2u),
              list<std::shared_ptr<rose<unsigned int>>>::ctor::cons_(
                  leaf(3u),
                  list<std::shared_ptr<rose<unsigned int>>>::ctor::nil_())));

  static inline const std::shared_ptr<rose<unsigned int>> bigger_tree =
      rose<unsigned int>::ctor::Node_(
          1u,
          list<std::shared_ptr<rose<unsigned int>>>::ctor::cons_(
              small_tree,
              list<std::shared_ptr<rose<unsigned int>>>::ctor::cons_(
                  leaf(4u),
                  list<std::shared_ptr<rose<unsigned int>>>::ctor::nil_())));

  static inline const unsigned int test_root_leaf =
      root<unsigned int>(leaf(5u));

  static inline const unsigned int test_root_small =
      root<unsigned int>(small_tree);

  static inline const unsigned int test_children_leaf =
      children_count<unsigned int>(leaf(5u));

  static inline const unsigned int test_children_small =
      children_count<unsigned int>(small_tree);

  static inline const unsigned int test_children_bigger =
      children_count<unsigned int>(bigger_tree);
};
