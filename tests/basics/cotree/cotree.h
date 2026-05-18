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
    A a;
    std::unique_ptr<List<A>> l;
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

  List(List<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) noexcept {
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
        _dst->v_ = Cons{_alt.a, _alt.l ? std::make_unique<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.l) {
          _stack.push_back({_alt.l.get(), _dst_alt.l.get()});
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
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a), l ? std::make_unique<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_unique<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
        if (_alt.l) {
          _stack.push_back(std::move(_alt.l));
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
      return List<T1>::cons(f(a0), a1->template map<T1>(f));
    }
  }
};

struct Cotree {
  template <typename A> struct colist {
    // TYPES
    struct Conil {};

    struct Cocons {
      A x;
      std::shared_ptr<colist<A>> xs;
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

    static colist<A> cocons(A x, const colist<A> &xs) {
      return colist(Cocons{std::move(x), std::make_shared<colist<A>>(xs)});
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
      A a;
      std::shared_ptr<colist<cotree<A>>> f;
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

    static cotree<A> conode(A a, const colist<cotree<A>> &f) {
      return cotree(
          Conode{std::move(a), std::make_shared<colist<cotree<A>>>(f)});
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
      A a;
      std::unique_ptr<List<tree<A>>> children;
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
        const auto &_alt = std::get<Node>(_src->v());
        _dst->v_ =
            Node{_alt.a,
                 _alt.children ? std::make_unique<List<tree<A>>>() : nullptr};
        auto &_dst_alt = std::get<Node>(_dst->v_);
        [&] {
          if (_alt.children) {
            const List<tree<A>> *_lsrc = _alt.children.get();
            List<tree<A>> *_ldst = _dst_alt.children.get();
            while (std::holds_alternative<typename List<tree<A>>::Cons>(
                _lsrc->v())) {
              const auto &_lsrc_c =
                  std::get<typename List<tree<A>>::Cons>(_lsrc->v());
              _ldst->v_mut() = typename List<tree<A>>::Cons{
                  tree<A>{},
                  _lsrc_c.l ? std::make_unique<List<tree<A>>>() : nullptr};
              auto &_ldst_c =
                  std::get<typename List<tree<A>>::Cons>(_ldst->v_mut());
              _stack.push_back({&_lsrc_c.a, &_ldst_c.a});
              if (_lsrc_c.l) {
                _lsrc = _lsrc_c.l.get();
                _ldst = _ldst_c.l.get();
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
      const auto &[a, children] = std::get<typename tree<_U>::Node>(_other.v());
      this->v_ =
          Node{A(a),
               children ? std::make_unique<List<tree<A>>>(*children) : nullptr};
    }

    static tree<A> node(A a, List<tree<A>> children) {
      return tree(Node{std::move(a),
                       std::make_unique<List<tree<A>>>(std::move(children))});
    }

    // MANIPULATORS
    ~tree() {
      std::vector<std::unique_ptr<tree<A>>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](tree<A> &_node) {
        if (std::holds_alternative<Node>(_node.v_)) {
          auto &_alt = std::get<Node>(_node.v_);
          if (_alt.children) {
            auto *_lp = _alt.children.get();
            while (std::holds_alternative<typename List<tree<A>>::Cons>(
                _lp->v())) {
              auto &_lc = std::get<typename List<tree<A>>::Cons>(_lp->v_mut());
              _stack.push_back(std::make_unique<tree<A>>(std::move(_lc.a)));
              if (_lc.l) {
                _lp = _lc.l.get();
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
  static List<T1> list_of_colist(uint64_t fuel, colist<T1> l) {
    if (fuel <= 0) {
      return List<T1>::nil();
    } else {
      uint64_t fuel_ = fuel - 1;
      if (std::holds_alternative<typename colist<T1>::Conil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename colist<T1>::Cocons>(l.v());
        return List<T1>::cons(a0, list_of_colist<T1>(fuel_, *a1));
      }
    }
  }

  template <typename T1>
  static tree<T1> tree_of_cotree(uint64_t fuel, cotree<T1> t) {
    const auto &[a0, a1] = std::get<typename cotree<T1>::Conode>(t.v());
    if (fuel <= 0) {
      return tree<T1>::node(a0, List<tree<T1>>::nil());
    } else {
      uint64_t fuel_ = fuel - 1;
      return tree<T1>::node(
          a0, list_of_colist<cotree<T1>>(fuel, *a1).template map<tree<T1>>(
                  [=](cotree<T1> _x0) mutable -> tree<T1> {
                    return tree_of_cotree<T1>(fuel_, _x0);
                  }));
    }
  }

  template <typename T1> static uint64_t tree_size(const tree<T1> &t) {
    const auto &[a0, a1] = std::get<typename tree<T1>::Node>(t.v());
    return ([&]() {
      auto aux_impl = [](auto &_self_aux, const List<tree<T1>> &l) -> uint64_t {
        if (std::holds_alternative<typename List<tree<T1>>::Nil>(l.v())) {
          return UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<tree<T1>>::Cons>(l.v());
          return (tree_size<T1>(a0) + _self_aux(_self_aux, *a1));
        }
      };
      auto aux = [&](const List<tree<T1>> &l) -> uint64_t {
        return aux_impl(aux_impl, l);
      };
      return aux(*a1);
    }() + 1);
  }

  static inline const cotree<uint64_t> sample_cotree = cotree<uint64_t>::conode(
      UINT64_C(1), colist<cotree<uint64_t>>::cocons(
                       singleton_cotree<uint64_t>(UINT64_C(2)),
                       colist<cotree<uint64_t>>::cocons(
                           singleton_cotree<uint64_t>(UINT64_C(3)),
                           colist<cotree<uint64_t>>::conil())));
  static inline const uint64_t test_root = sample_cotree.root();
  static inline const uint64_t test_doubled_root =
      sample_cotree
          .template comap_cotree<uint64_t>(
              [](uint64_t n) { return (n * UINT64_C(2)); })
          .root();
  static colist<uint64_t> nats(uint64_t n);
  static inline const List<uint64_t> test_first_five =
      list_of_colist<uint64_t>(UINT64_C(5), nats(UINT64_C(0)));
  static colist<uint64_t> binary_children(uint64_t n);
  static inline const cotree<uint64_t> binary_tree =
      unfold_cotree<uint64_t>(binary_children, UINT64_C(0));
  static inline const uint64_t test_binary_root = binary_tree.root();
  static inline const tree<uint64_t> test_approx =
      tree_of_cotree<uint64_t>(UINT64_C(2), binary_tree);
  static inline const uint64_t test_approx_root =
      tree_root<uint64_t>(test_approx);

  static inline const uint64_t test_approx_size =
      tree_size<uint64_t>(test_approx);
};

#endif // INCLUDED_COTREE
