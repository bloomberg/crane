#ifndef INCLUDED_COTREE
#define INCLUDED_COTREE

#include "crane_fn.h"
#include "fn.h"
#include "lazy.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;

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

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) = default;
  List &operator=(List &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const A &>
  List<T1> map(F0 &&f) const {
    std::optional<List<T1>> _root{};
    std::shared_ptr<List<T1>> *_write = nullptr;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = List<T1>::nil();
        (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell = typename List<T1>::Cons(f(a0), nullptr);
        List<T1> &_node =
            (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<T1>::Cons>(_node.v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }
};

struct Cotree {
  template <typename A> struct colist {
    // TYPES
    struct Conil {};

    template <typename CraneS0 = colist<A>> struct Cocons_ {
      A x;
      CraneS0 xs;
    };

    using Cocons = Cocons_<>;
    using variant_t = std::variant<Conil, Cocons>;

  private:
    // DATA
    crane::lazy<variant_t> lazy_v_;

  public:
    // CREATORS
    colist() {}

    explicit colist(Conil _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit colist(Cocons _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    template <typename CraneU>
    colist(const colist<CraneU> &_other)
        : lazy_v_(crane::lazy<variant_t>::converted_from(
              _other.lazy_cell(), [=]() -> variant_t {
                if (std::holds_alternative<typename colist<CraneU>::Conil>(
                        _other.v())) {
                  return Conil{};
                } else {
                  const auto &[x, xs] =
                      std::get<typename colist<CraneU>::Cocons>(_other.v());
                  return Cocons{
                      [&]() -> A {
                        if constexpr (crane_convertible<A, const CraneU &>) {
                          return crane_convert<A>(x);
                        } else {
                          throw std::logic_error(
                              "unreachable: inactive constructor field at this "
                              "instantiation");
                        }
                      }(),
                      crane_convert<colist<A>>(xs)};
                }
              })) {}

    explicit colist(crane::fn<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static colist<A> conil() {
      return colist<A>(
          crane::lazy<variant_t>(std::in_place, std::in_place_index<0>));
    }

    static colist<A> cocons(A x, colist<A> xs) {
      return colist<A>(crane::lazy<variant_t>(
          std::in_place, std::in_place_index<1>, std::move(x), std::move(xs)));
    }

    explicit colist(crane::lazy<variant_t> _cell) : lazy_v_(std::move(_cell)) {}

    template <typename F> static colist<A> lazy_(F &&thunk) {
      return colist<A>(
          crane::lazy<variant_t>::delegate(std::forward<F>(thunk)));
    }

    // ACCESSORS
    const variant_t &v() const { return lazy_v_.force(); }

    const crane::lazy<variant_t> &lazy_cell() const { return lazy_v_; }
  };

  template <typename A> struct cotree {
    // TYPES
    template <typename CraneS0 = cotree<A>> struct Conode_ {
      A a;
      colist<CraneS0> f;
    };

    using Conode = Conode_<>;
    using variant_t = std::variant<Conode>;

  private:
    // DATA
    crane::lazy<variant_t> lazy_v_;

  public:
    // CREATORS
    cotree() {}

    explicit cotree(Conode _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    template <typename CraneU>
    cotree(const cotree<CraneU> &_other)
        : lazy_v_(crane::lazy<variant_t>::converted_from(
              _other.lazy_cell(), [=]() -> variant_t {
                const auto &[a, f] =
                    std::get<typename cotree<CraneU>::Conode>(_other.v());
                return Conode{
                    [&]() -> A {
                      if constexpr (crane_convertible<A, const CraneU &>) {
                        return crane_convert<A>(a);
                      } else {
                        throw std::logic_error(
                            "unreachable: inactive constructor field at this "
                            "instantiation");
                      }
                    }(),
                    crane_convert<colist<cotree<A>>>(f)};
              })) {}

    explicit cotree(crane::fn<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static cotree<A> conode(A a, colist<cotree<A>> f) {
      return cotree<A>(crane::lazy<variant_t>(
          std::in_place, std::in_place_index<0>, std::move(a), std::move(f)));
    }

    explicit cotree(crane::lazy<variant_t> _cell) : lazy_v_(std::move(_cell)) {}

    template <typename F> static cotree<A> lazy_(F &&thunk) {
      return cotree<A>(
          crane::lazy<variant_t>::delegate(std::forward<F>(thunk)));
    }

    // ACCESSORS
    const variant_t &v() const { return lazy_v_.force(); }

    const crane::lazy<variant_t> &lazy_cell() const { return lazy_v_; }

    const A &root() const & {
      const auto &[a0, a1] = std::get<typename cotree<A>::Conode>(this->v());
      return a0;
    }

    A root() const && {
      const auto &[a0, a1] = std::get<typename cotree<A>::Conode>(this->v());
      return a0;
    }

    const colist<cotree<A>> &children() const & {
      const auto &[a0, a1] = std::get<typename cotree<A>::Conode>(this->v());
      return a1;
    }

    colist<cotree<A>> children() const && {
      const auto &[a0, a1] = std::get<typename cotree<A>::Conode>(this->v());
      return a1;
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, const F0 &, const A &>
    cotree<T1> comap_cotree(F0 &&g) const {
      const auto &[a0, a1] = std::get<typename cotree<A>::Conode>(this->v());
      return cotree<T1>::lazy_([=]() -> cotree<T1> {
        return cotree<T1>::conode(g(a0),
                                  comap<cotree<A>, cotree<T1>>(
                                      [=](cotree<A> _x0) -> cotree<T1> {
                                        return _x0.template comap_cotree<T1>(g);
                                      },
                                      a1));
      });
    }
  };

  template <typename A> struct tree {
    // TYPES
    struct Node {
      A a;
      std::shared_ptr<List<tree<A>>> children;
    };

    using variant_t = std::variant<Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Node _v) : v_(std::move(_v)) {}

    template <typename CraneU>
    tree(const tree<CraneU> &_other)
        : v_([&]() -> variant_t {
            const auto &[a, children] =
                std::get<typename tree<CraneU>::Node>(_other.v());
            return Node{[&]() -> A {
                          if constexpr (crane_convertible<A, const CraneU &>) {
                            return crane_convert<A>(a);
                          } else {
                            throw std::logic_error(
                                "unreachable: inactive constructor field at "
                                "this instantiation");
                          }
                        }(),
                        (children ? std::make_shared<List<tree<A>>>(
                                        crane_convert<List<tree<A>>>(*children))
                                  : nullptr)};
          }()) {}

    static tree<A> node(A a, List<tree<A>> children) {
      return tree<A>(Node{
          std::move(a), std::make_shared<List<tree<A>>>(std::move(children))});
    }

    // MANIPULATORS
    ~tree() {
      crane::small_vector<std::shared_ptr<tree<A>>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->children && _alt->children.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            auto _lp = _alt->children.get();
            while (std::holds_alternative<typename List<tree<A>>::Cons>(
                _lp->v())) {
              auto &_lc = std::get<typename List<tree<A>>::Cons>(_lp->v_mut());
              _stack.push_back(std::make_shared<tree<A>>(std::move(_lc.a)));
              if (_lc.l && _lc.l.use_count() == 1) {
                std::atomic_thread_fence(std::memory_order_acquire);
                _lp = _lc.l.get();
              } else {
                break;
              }
            }
            _alt->children.reset();
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          _drain(_cur->v_mut());
        }
      }
    }

    tree(const tree &) = default;
    tree &operator=(const tree &) = default;
    tree(tree &&) = default;
    tree &operator=(tree &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F0>
  static T2 tree_rect(F0 &&f, const tree<T1> &t) {
    const auto &[a0, a1] = std::get<typename tree<T1>::Node>(t.v());
    return f(a0, *a1);
  }

  template <typename T1, typename T2, typename F0>
  static T2 tree_rec(F0 &&f, const tree<T1> &t) {
    return tree_rect<T1, T2>(f, t);
  }

  template <typename T1> static T1 tree_root(const tree<T1> &t) {
    const auto &[a0, a1] = std::get<typename tree<T1>::Node>(t.v());
    return a0;
  }

  template <typename T1, typename T2>
  static colist<T2> comap(const std::type_identity_t<crane::fn<T2(T1)>> &f,
                          const colist<T1> &l) {
    if (std::holds_alternative<typename colist<T1>::Conil>(l.v())) {
      return colist<T2>::conil();
    } else {
      const auto &[a0, a1] = std::get<typename colist<T1>::Cocons>(l.v());
      return colist<T2>::lazy_([=]() -> colist<T2> {
        return colist<T2>::cocons(f(a0), comap<T1, T2>(f, a1));
      });
    }
  }

  template <typename T1> static cotree<T1> singleton_cotree(const T1 &a) {
    return cotree<T1>::conode(a, colist<cotree<T1>>::conil());
  }

  template <typename T1>
  static cotree<T1>
  unfold_cotree(const std::type_identity_t<crane::fn<colist<T1>(T1)>> &next,
                const T1 &init) {
    return cotree<T1>::lazy_([=]() -> cotree<T1> {
      return cotree<T1>::conode(init, comap<T1, cotree<T1>>(
                                          [=](T1 _x0) -> cotree<T1> {
                                            return unfold_cotree<T1>(next, _x0);
                                          },
                                          next(init)));
    });
  }

  template <typename T1>
  static List<T1> list_of_colist(uint64_t fuel, const colist<T1> &l) {
    if (fuel <= 0) {
      return List<T1>::nil();
    } else {
      uint64_t fuel_ = fuel - 1;
      if (std::holds_alternative<typename colist<T1>::Conil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename colist<T1>::Cocons>(l.v());
        return List<T1>::cons(a0, list_of_colist<T1>(fuel_, a1));
      }
    }
  }

  template <typename T1>
  static tree<T1> tree_of_cotree(uint64_t fuel, const cotree<T1> &t) {
    const auto &[a0, a1] = std::get<typename cotree<T1>::Conode>(t.v());
    if (fuel <= 0) {
      return tree<T1>::node(a0, List<tree<T1>>::nil());
    } else {
      uint64_t fuel_ = fuel - 1;
      return tree<T1>::node(
          a0, list_of_colist<cotree<T1>>(fuel, a1).template map<tree<T1>>(
                  [=](cotree<T1> _x0) -> tree<T1> {
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
          const auto &[a2, a3] = std::get<typename List<tree<T1>>::Cons>(l.v());
          return (tree_size<T1>(a2) + _self_aux(_self_aux, *a3));
        }
      };
      auto aux = [&](const List<tree<T1>> &l) -> uint64_t {
        return aux_impl(aux_impl, l);
      };
      return aux(*a1);
    }() + 1);
  }

  static inline const cotree<uint64_t> sample_cotree =
      cotree<uint64_t>::lazy_([]() -> cotree<uint64_t> {
        return cotree<uint64_t>::conode(
            UINT64_C(1),
            colist<cotree<uint64_t>>::lazy_([]() -> colist<cotree<uint64_t>> {
              return colist<cotree<uint64_t>>::cocons(
                  singleton_cotree<uint64_t>(UINT64_C(2)),
                  colist<cotree<uint64_t>>::lazy_(
                      []() -> colist<cotree<uint64_t>> {
                        return colist<cotree<uint64_t>>::cocons(
                            singleton_cotree<uint64_t>(UINT64_C(3)),
                            colist<cotree<uint64_t>>::conil());
                      }));
            }));
      });
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
