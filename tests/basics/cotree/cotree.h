#ifndef INCLUDED_COTREE
#define INCLUDED_COTREE

#include "lazy.h"
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a0;
    std::unique_ptr<List<A>> a1;
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

  List(const List<A> &_other) : v_(std::move(_other.clone().v_)) {}

  List(List<A> &&_other) : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  List<A> clone() const {
    List<A> _out{};

    struct _CloneFrame {
      const List<A> *_src;
      List<A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<A> *_src = _frame._src;
      List<A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->v_ =
            Cons{_alt.a0, _alt.a1 ? std::make_unique<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.a1) {
          _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a0, a1] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a0), a1 ? std::make_unique<List<A>>(*a1) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a0, List<A> a1) {
    return List(Cons{std::move(a0), std::make_unique<List<A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
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

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, A &>
  List<T1> map(F0 &&f) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return List<T1>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return List<T1>::cons(f(a0), (*a1).template map<T1>(f));
    }
  }
};

struct Cotree {
  template <typename A> struct colist {
    // TYPES
    struct Conil {};

    struct Cocons {
      A a0;
      std::shared_ptr<colist<A>> a1;
    };

    using variant_t = std::variant<Conil, Cocons>;

  private:
    // DATA
    crane::lazy<variant_t> lazy_v_;

  public:
    // CREATORS
    explicit colist(Conil _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit colist(Cocons _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit colist(std::function<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static colist<A> conil() { return colist(Conil{}); }

    static colist<A> cocons(A a0, const colist<A> &a1) {
      return colist(Cocons{std::move(a0), std::make_shared<colist<A>>(a1)});
    }

    static colist<A> lazy_(std::function<colist<A>()> thunk) {
      return colist<A>(std::function<variant_t()>([=]() mutable -> variant_t {
        colist<A> _tmp = thunk();
        return _tmp.v();
      }));
    }

    // ACCESSORS
    const variant_t &v() const { return lazy_v_.force(); }
  };

  template <typename A> struct cotree {
    // TYPES
    struct Conode {
      A a0;
      std::shared_ptr<colist<cotree<A>>> a1;
    };

    using variant_t = std::variant<Conode>;

  private:
    // DATA
    crane::lazy<variant_t> lazy_v_;

  public:
    // CREATORS
    explicit cotree(Conode _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit cotree(std::function<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static cotree<A> conode(A a0, const colist<cotree<A>> &a1) {
      return cotree(
          Conode{std::move(a0), std::make_shared<colist<cotree<A>>>(a1)});
    }

    static cotree<A> lazy_(std::function<cotree<A>()> thunk) {
      return cotree<A>(std::function<variant_t()>([=]() mutable -> variant_t {
        cotree<A> _tmp = thunk();
        return _tmp.v();
      }));
    }

    // ACCESSORS
    const variant_t &v() const { return lazy_v_.force(); }

    A root() const {
      const auto &[a0, a1] = std::get<typename cotree<A>::Conode>(this->v());
      return a0;
    }

    colist<cotree<A>> children() const {
      const auto &[a0, a1] = std::get<typename cotree<A>::Conode>(this->v());
      return colist<std::shared_ptr<cotree<A>>>::lazy_(
          [=]() mutable -> colist<cotree<A>> { return *a1; });
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &>
    cotree<T1> comap_cotree(F0 &&g) const {
      const auto &[a0, a1] = std::get<typename cotree<A>::Conode>(this->v());
      return cotree<T1>::lazy_([=]() mutable -> cotree<T1> {
        return cotree<T1>::conode(g(a0),
                                  comap<cotree<A>, cotree<T1>>(
                                      [=](cotree<A> _x0) mutable -> cotree<T1> {
                                        return _x0.template comap_cotree<T1>(g);
                                      },
                                      *a1));
      });
    }
  };

  template <typename A> struct tree {
    // TYPES
    struct Node {
      A a0;
      std::unique_ptr<List<tree<A>>> a1;
    };

    using variant_t = std::variant<Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree() {}

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
        const auto &_alt = std::get<Node>(_src->v());
        _dst->v_ = Node{_alt.a0,
                        _alt.a1 ? std::make_unique<List<tree<A>>>() : nullptr};
        auto &_dst_alt = std::get<Node>(_dst->v_);
        [&] {
          if (_alt.a1) {
            const List<tree<A>> *_lsrc = _alt.a1.get();
            List<tree<A>> *_ldst = _dst_alt.a1.get();
            while (std::holds_alternative<typename List<tree<A>>::Cons>(
                _lsrc->v())) {
              const auto &_lsrc_c =
                  std::get<typename List<tree<A>>::Cons>(_lsrc->v());
              _ldst->v_mut() = typename List<tree<A>>::Cons{
                  tree<A>{},
                  _lsrc_c.a1 ? std::make_unique<List<tree<A>>>() : nullptr};
              auto &_ldst_c =
                  std::get<typename List<tree<A>>::Cons>(_ldst->v_mut());
              _stack.push_back({&_lsrc_c.a0, &_ldst_c.a0});
              if (_lsrc_c.a1) {
                _lsrc = _lsrc_c.a1.get();
                _ldst = _ldst_c.a1.get();
              } else {
                break;
              }
            }
            if (std::holds_alternative<typename List<tree<A>>::Nil>(
                    _lsrc->v())) {
              _ldst->v_mut() = typename List<tree<A>>::Nil{};
            }
          }
        }();
      }
      return _out;
    }

    // CREATORS
    template <typename _U> explicit tree(const tree<_U> &_other) {
      const auto &[a0, a1] = std::get<typename tree<_U>::Node>(_other.v());
      this->v_ =
          Node{A(a0), a1 ? std::make_unique<List<tree<A>>>(*a1) : nullptr};
    }

    static tree<A> node(A a0, List<tree<A>> a1) {
      return tree(
          Node{std::move(a0), std::make_unique<List<tree<A>>>(std::move(a1))});
    }

    // MANIPULATORS
    ~tree() {
      std::vector<std::unique_ptr<tree<A>>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](tree<A> &_node) {
        if (std::holds_alternative<Node>(_node.v_)) {
          auto &_alt = std::get<Node>(_node.v_);
          if (_alt.a1) {
            auto *_lp = _alt.a1.get();
            while (std::holds_alternative<typename List<tree<A>>::Cons>(
                _lp->v())) {
              auto &_lc = std::get<typename List<tree<A>>::Cons>(_lp->v_mut());
              _stack.push_back(std::make_unique<tree<A>>(std::move(_lc.a0)));
              if (_lc.a1) {
                _lp = _lc.a1.get();
              } else {
                break;
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

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &, List<tree<T1>> &>
  static T2 tree_rect(F0 &&f, const tree<T1> &t) {
    const auto &[a0, a1] = std::get<typename tree<T1>::Node>(t.v());
    return f(a0, *a1);
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &, List<tree<T1>> &>
  static T2 tree_rec(F0 &&f, const tree<T1> &t) {
    const auto &[a0, a1] = std::get<typename tree<T1>::Node>(t.v());
    return f(a0, *a1);
  }

  template <typename T1> static T1 tree_root(const tree<T1> &t) {
    const auto &[a0, a1] = std::get<typename tree<T1>::Node>(t.v());
    return a0;
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static colist<T2> comap(F0 &&f, colist<T1> l) {
    if (std::holds_alternative<typename colist<T1>::Conil>(l.v())) {
      return colist<T2>::lazy_(
          []() -> colist<T2> { return colist<T2>::conil(); });
    } else {
      const auto &[a0, a1] = std::get<typename colist<T1>::Cocons>(l.v());
      return colist<T2>::lazy_([=]() mutable -> colist<T2> {
        return colist<T2>::cocons(f(a0), comap<T1, T2>(f, *a1));
      });
    }
  }

  template <typename T1> static cotree<T1> singleton_cotree(T1 a) {
    return cotree<T1>::lazy_([=]() mutable -> cotree<T1> {
      return cotree<T1>::conode(a, colist<cotree<T1>>::conil());
    });
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<colist<T1>, F0 &, T1 &>
  static cotree<T1> unfold_cotree(F0 &&next, T1 init) {
    return cotree<T1>::lazy_([=]() mutable -> cotree<T1> {
      return cotree<T1>::conode(init, comap<T1, cotree<T1>>(
                                          [=](T1 _x0) mutable -> cotree<T1> {
                                            return unfold_cotree<T1>(next, _x0);
                                          },
                                          next(init)));
    });
  }

  template <typename T1>
  static List<T1> list_of_colist(unsigned int fuel, colist<T1> l) {
    if (fuel <= 0) {
      return List<T1>::nil();
    } else {
      unsigned int fuel_ = fuel - 1;
      if (std::holds_alternative<typename colist<T1>::Conil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename colist<T1>::Cocons>(l.v());
        return List<T1>::cons(a0, list_of_colist<T1>(fuel_, *a1));
      }
    }
  }

  template <typename T1>
  static tree<T1> tree_of_cotree(unsigned int fuel, cotree<T1> t) {
    const auto &[a0, a1] = std::get<typename cotree<T1>::Conode>(t.v());
    if (fuel <= 0) {
      return tree<T1>::node(a0, List<tree<T1>>::nil());
    } else {
      unsigned int fuel_ = fuel - 1;
      return tree<T1>::node(
          a0, list_of_colist<cotree<T1>>(fuel, *a1).template map<tree<T1>>(
                  [=](cotree<T1> _x0) mutable -> tree<T1> {
                    return tree_of_cotree<T1>(fuel_, _x0);
                  }));
    }
  }

  template <typename T1> static unsigned int tree_size(const tree<T1> &t) {
    const auto &[a0, a1] = std::get<typename tree<T1>::Node>(t.v());
    return ([&]() {
      auto aux_impl = [](auto &_self_aux,
                         const List<tree<T1>> &l) -> unsigned int {
        if (std::holds_alternative<typename List<tree<T1>>::Nil>(l.v())) {
          return 0u;
        } else {
          const auto &[a0, a1] = std::get<typename List<tree<T1>>::Cons>(l.v());
          return (tree_size<T1>(a0) + _self_aux(_self_aux, *a1));
        }
      };
      auto aux = [&](const List<tree<T1>> &l) -> unsigned int {
        return aux_impl(aux_impl, l);
      };
      return aux(*a1);
    }() + 1);
  }

  static inline const cotree<unsigned int> sample_cotree =
      cotree<unsigned int>::conode(
          1u, colist<cotree<unsigned int>>::cocons(
                  singleton_cotree<unsigned int>(2u),
                  colist<cotree<unsigned int>>::cocons(
                      singleton_cotree<unsigned int>(3u),
                      colist<cotree<unsigned int>>::conil())));
  static inline const unsigned int test_root = sample_cotree.root();
  static inline const unsigned int test_doubled_root =
      sample_cotree
          .template comap_cotree<unsigned int>(
              [](unsigned int n) { return (n * 2u); })
          .root();
  static colist<unsigned int> nats(unsigned int n);
  static inline const List<unsigned int> test_first_five =
      list_of_colist<unsigned int>(5u, nats(0u));
  static colist<unsigned int> binary_children(unsigned int n);
  static inline const cotree<unsigned int> binary_tree =
      unfold_cotree<unsigned int>(binary_children, 0u);
  static inline const unsigned int test_binary_root = binary_tree.root();
  static inline const tree<unsigned int> test_approx =
      tree_of_cotree<unsigned int>(2u, binary_tree);
  static inline const unsigned int test_approx_root =
      tree_root<unsigned int>(test_approx);

  static inline const unsigned int test_approx_size =
      tree_size<unsigned int>(test_approx);
};

#endif // INCLUDED_COTREE
