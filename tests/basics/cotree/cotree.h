#ifndef INCLUDED_COTREE
#define INCLUDED_COTREE

#include "lazy.h"
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
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  template <typename T1, MapsTo<T1, t_A> F0>
  __attribute__((pure)) List<T1> map(F0 &&f) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return List<T1>::nil();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return List<T1>::cons(f(d_a0), (*(d_a1)).template map<T1>(f));
    }
  }
};

struct Cotree {
  template <typename t_A> struct colist {
    // TYPES
    struct Conil {};

    struct Cocons {
      t_A d_a0;
      std::shared_ptr<colist<t_A>> d_a1;
    };

    using variant_t = std::variant<Conil, Cocons>;

  private:
    // DATA
    crane::lazy<variant_t> d_lazyV_;

  public:
    // CREATORS
    explicit colist(Conil _v)
        : d_lazyV_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit colist(Cocons _v)
        : d_lazyV_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit colist(std::function<variant_t()> _thunk)
        : d_lazyV_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static std::shared_ptr<colist<t_A>> conil() {
      return std::make_shared<colist<t_A>>(Conil{});
    }

    static std::shared_ptr<colist<t_A>>
    cocons(t_A a0, std::shared_ptr<colist<t_A>> a1) {
      return std::make_shared<colist<t_A>>(
          Cocons{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<colist<t_A>>
    lazy_(std::function<std::shared_ptr<colist<t_A>>()> thunk) {
      return std::make_shared<colist<t_A>>(
          std::function<variant_t()>([=]() mutable -> variant_t {
            std::shared_ptr<colist<t_A>> _tmp = thunk();
            return _tmp->v();
          }));
    }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const {
      return d_lazyV_.force();
    }
  };

  template <typename t_A> struct cotree {
    // TYPES
    struct Conode {
      t_A d_a0;
      std::shared_ptr<colist<std::shared_ptr<cotree<t_A>>>> d_a1;
    };

    using variant_t = std::variant<Conode>;

  private:
    // DATA
    crane::lazy<variant_t> d_lazyV_;

  public:
    // CREATORS
    explicit cotree(Conode _v)
        : d_lazyV_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit cotree(std::function<variant_t()> _thunk)
        : d_lazyV_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static std::shared_ptr<cotree<t_A>>
    conode(t_A a0, std::shared_ptr<colist<std::shared_ptr<cotree<t_A>>>> a1) {
      return std::make_shared<cotree<t_A>>(
          Conode{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<cotree<t_A>>
    lazy_(std::function<std::shared_ptr<cotree<t_A>>()> thunk) {
      return std::make_shared<cotree<t_A>>(
          std::function<variant_t()>([=]() mutable -> variant_t {
            std::shared_ptr<cotree<t_A>> _tmp = thunk();
            return _tmp->v();
          }));
    }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const {
      return d_lazyV_.force();
    }

    t_A root() const {
      const auto &[d_a0, d_a1] =
          std::get<typename cotree<t_A>::Conode>(this->v());
      return d_a0;
    }

    std::shared_ptr<colist<std::shared_ptr<cotree<t_A>>>> children() const {
      const auto &[d_a0, d_a1] =
          std::get<typename cotree<t_A>::Conode>(this->v());
      return colist<std::shared_ptr<cotree<t_A>>>::lazy_(
          [=]() mutable
              -> std::shared_ptr<colist<std::shared_ptr<cotree<t_A>>>> {
            return d_a1;
          });
    }

    template <typename T1, MapsTo<T1, t_A> F0>
    std::shared_ptr<cotree<T1>> comap_cotree(F0 &&g) const {
      const auto &[d_a0, d_a1] =
          std::get<typename cotree<t_A>::Conode>(this->v());
      return cotree<T1>::lazy_([=]() mutable -> std::shared_ptr<cotree<T1>> {
        return cotree<T1>::conode(
            g(d_a0),
            comap<std::shared_ptr<cotree<t_A>>, std::shared_ptr<cotree<T1>>>(
                [=](const std::shared_ptr<cotree<t_A>> &_x0) mutable
                    -> std::shared_ptr<cotree<T1>> {
                  return _x0->template comap_cotree<T1>(g);
                },
                d_a1));
      });
    }
  };

  template <typename t_A> struct tree {
    // TYPES
    struct Node {
      t_A d_a0;
      std::unique_ptr<List<tree<t_A>>> d_a1;
    };

    using variant_t = std::variant<Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    tree() {}

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
    __attribute__((pure)) tree<t_A> clone() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<Node>(_sv.v());
      return tree<t_A>(Node{
          d_a0, d_a1 ? std::make_unique<List<Cotree::tree<t_A>>>(d_a1->clone())
                     : nullptr});
    }

    // CREATORS
    template <typename _U> explicit tree(const tree<_U> &_other) {
      const auto &[d_a0, d_a1] = std::get<typename tree<_U>::Node>(_other.v());
      d_v_ = Node{t_A(d_a0),
                  d_a1 ? std::make_unique<List<tree<t_A>>>(*d_a1) : nullptr};
    }

    __attribute__((pure)) static tree<t_A> node(t_A a0,
                                                const List<tree<t_A>> &a1) {
      return tree(Node{std::move(a0), std::make_unique<List<tree<t_A>>>(a1)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, MapsTo<T2, T1, List<tree<T1>>> F0>
  static T2 tree_rect(F0 &&f, const tree<T1> &t) {
    const auto &[d_a0, d_a1] = std::get<typename tree<T1>::Node>(t.v());
    return f(d_a0, *(d_a1));
  }

  template <typename T1, typename T2, MapsTo<T2, T1, List<tree<T1>>> F0>
  static T2 tree_rec(F0 &&f, const tree<T1> &t) {
    const auto &[d_a0, d_a1] = std::get<typename tree<T1>::Node>(t.v());
    return f(d_a0, *(d_a1));
  }

  template <typename T1> static T1 tree_root(const tree<T1> &t) {
    const auto &[d_a0, d_a1] = std::get<typename tree<T1>::Node>(t.v());
    return d_a0;
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static std::shared_ptr<colist<T2>>
  comap(F0 &&f, const std::shared_ptr<colist<T1>> &l) {
    if (std::holds_alternative<typename colist<T1>::Conil>(l->v())) {
      return colist<T2>::lazy_(
          []() -> std::shared_ptr<colist<T2>> { return colist<T2>::conil(); });
    } else {
      const auto &[d_a0, d_a1] = std::get<typename colist<T1>::Cocons>(l->v());
      return colist<T2>::lazy_([=]() mutable -> std::shared_ptr<colist<T2>> {
        return colist<T2>::cocons(f(d_a0), comap<T1, T2>(f, d_a1));
      });
    }
  }

  template <typename T1>
  static std::shared_ptr<cotree<T1>> singleton_cotree(const T1 a) {
    return cotree<T1>::lazy_([=]() mutable -> std::shared_ptr<cotree<T1>> {
      return cotree<T1>::conode(a,
                                colist<std::shared_ptr<cotree<T1>>>::conil());
    });
  }

  template <typename T1, MapsTo<std::shared_ptr<colist<T1>>, T1> F0>
  static std::shared_ptr<cotree<T1>> unfold_cotree(F0 &&next, const T1 init) {
    return cotree<T1>::lazy_([=]() mutable -> std::shared_ptr<cotree<T1>> {
      return cotree<T1>::conode(
          init, comap<T1, std::shared_ptr<cotree<T1>>>(
                    [=](T1 _x0) mutable -> std::shared_ptr<cotree<T1>> {
                      return unfold_cotree<T1>(next, _x0);
                    },
                    next(init)));
    });
  }

  template <typename T1>
  __attribute__((pure)) static List<T1>
  list_of_colist(const unsigned int &fuel,
                 const std::shared_ptr<colist<T1>> &l) {
    if (fuel <= 0) {
      return List<T1>::nil();
    } else {
      unsigned int fuel_ = fuel - 1;
      if (std::holds_alternative<typename colist<T1>::Conil>(l->v())) {
        return List<T1>::nil();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename colist<T1>::Cocons>(l->v());
        return List<T1>::cons(d_a0, list_of_colist<T1>(fuel_, d_a1));
      }
    }
  }

  template <typename T1>
  __attribute__((pure)) static tree<T1>
  tree_of_cotree(const unsigned int &fuel,
                 const std::shared_ptr<cotree<T1>> &t) {
    const auto &[d_a0, d_a1] = std::get<typename cotree<T1>::Conode>(t->v());
    if (fuel <= 0) {
      return tree<T1>::node(d_a0, List<tree<T1>>::nil());
    } else {
      unsigned int fuel_ = fuel - 1;
      return tree<T1>::node(
          d_a0,
          list_of_colist<std::shared_ptr<cotree<T1>>>(fuel, d_a1)
              .template map<tree<T1>>(
                  [=](const std::shared_ptr<cotree<T1>> &_x0) mutable
                      -> tree<T1> { return tree_of_cotree<T1>(fuel_, _x0); }));
    }
  }

  template <typename T1>
  __attribute__((pure)) static unsigned int tree_size(const tree<T1> &t) {
    const auto &[d_a0, d_a1] = std::get<typename tree<T1>::Node>(t.v());
    List<tree<T1>> d_a1_value = List<Cotree::tree<T1>>(*(d_a1));
    return ([&]() {
      std::function<unsigned int(List<tree<T1>>)> aux;
      aux = [&](List<tree<T1>> l) -> unsigned int {
        if (std::holds_alternative<typename List<tree<T1>>::Nil>(l.v())) {
          return 0u;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<tree<T1>>::Cons>(l.v());
          return (tree_size<T1>(d_a0) + aux(*(d_a1)));
        }
      };
      return aux(d_a1_value);
    }() + 1);
  }

  static inline const std::shared_ptr<cotree<unsigned int>> sample_cotree =
      cotree<unsigned int>::conode(
          1u, colist<std::shared_ptr<cotree<unsigned int>>>::cocons(
                  singleton_cotree<unsigned int>(2u),
                  colist<std::shared_ptr<cotree<unsigned int>>>::cocons(
                      singleton_cotree<unsigned int>(3u),
                      colist<std::shared_ptr<cotree<unsigned int>>>::conil())));
  static inline const unsigned int test_root = sample_cotree->root();
  static inline const unsigned int test_doubled_root =
      sample_cotree
          ->template comap_cotree<unsigned int>(
              [](const unsigned int &n) { return (n * 2u); })
          ->root();
  static std::shared_ptr<colist<unsigned int>> nats(unsigned int n);
  static inline const List<unsigned int> test_first_five =
      list_of_colist<unsigned int>(5u, nats(0u));
  static std::shared_ptr<colist<unsigned int>>
  binary_children(const unsigned int &n);
  static inline const std::shared_ptr<cotree<unsigned int>> binary_tree =
      unfold_cotree<unsigned int>(binary_children, 0u);
  static inline const unsigned int test_binary_root = binary_tree->root();
  static inline const tree<unsigned int> test_approx =
      tree_of_cotree<unsigned int>(2u, binary_tree);
  static inline const unsigned int test_approx_root =
      tree_root<unsigned int>(test_approx);
  static inline const unsigned int test_approx_size =
      tree_size<unsigned int>(test_approx);
};

#endif // INCLUDED_COTREE
