#ifndef INCLUDED_POINT_FREE_FIX_BINDER_UNTYPED
#define INCLUDED_POINT_FREE_FIX_BINDER_UNTYPED

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

struct option_monad;
struct Nat;
template <typename A> struct List;
template <typename base> struct Tree;
struct nat_params;
struct c1n;
struct c2n;
struct c3n;
struct c4n;
using base = crane::obj;
template <typename I>
concept Monad = requires {
  typename I::template m<crane::obj>;
  {
    I::template ret<crane::obj>(std::declval<crane::obj>())
  } -> std::convertible_to<typename I::template m<crane::obj>>;
  {
    I::template bind<crane::obj, crane::obj>(
        std::declval<typename I::template m<crane::obj>>(),
        std::declval<
            crane::fn<typename I::template m<crane::obj>(crane::obj)>>())
  } -> std::convertible_to<typename I::template m<crane::obj>>;
};
template <typename
I>concept Params = requires {
    typename I::base;
  } && (requires {
    { I::base_default() } -> std::convertible_to<typename I::base>;
  } || requires {
    { I::base_default } -> std::convertible_to<typename I::base>;
  });
template <typename I, typename X>
concept C1 = requires {
  { I::c1(std::declval<X>()) } -> std::convertible_to<X>;
};
template <typename I, typename X>
concept C2 = requires {
  { I::c2(std::declval<X>()) } -> std::convertible_to<X>;
};
template <typename I, typename X>
concept C3 = requires {
  { I::c3(std::declval<X>()) } -> std::convertible_to<X>;
};
template <typename I, typename X>
concept C4 = requires {
  { I::c4(std::declval<X>()) } -> std::convertible_to<X>;
};

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Nat() {}

  explicit Nat(O _v) : v_(_v) {}

  explicit Nat(S _v) : v_(std::move(_v)) {}

  static Nat o() { return Nat(O{}); }

  static Nat s(Nat a0) { return Nat(S{std::make_shared<Nat>(std::move(a0))}); }

  // MANIPULATORS
  ~Nat() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<Nat> {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      return nullptr;
    };
    std::shared_ptr<Nat> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  Nat(const Nat &) = default;
  Nat &operator=(const Nat &) = default;
  Nat(Nat &&) = default;
  Nat &operator=(Nat &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

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
      : v_(crane_convert_spine(
            _other, std::shared_ptr<List<A>>(nullptr),
            [](const List<CraneU> &_cell) -> const List<CraneU> * {
              if (std::holds_alternative<typename List<CraneU>::Cons>(
                      _cell.v())) {
                return std::get<typename List<CraneU>::Cons>(_cell.v()).l.get();
              } else {
                return nullptr;
              }
            },
            [&](const List<CraneU> &_other,
                std::shared_ptr<List<A>> _below) -> variant_t {
              if (std::holds_alternative<typename List<CraneU>::Nil>(
                      _other.v())) {
                return Nil{};
              } else {
                const auto &[a, l] =
                    std::get<typename List<CraneU>::Cons>(_other.v());
                return Cons{
                    [&]() -> A {
                      if constexpr (crane_convertible<A, const CraneU &>) {
                        return crane_convert<A>(a);
                      } else {
                        throw std::logic_error(
                            "unreachable: inactive constructor field at this "
                            "instantiation");
                      }
                    }(),
                    std::move(_below)};
              }
            },
            [](auto &&_alt) {
              return std::make_shared<List<A>>(std::move(_alt));
            })) {}

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
};

template <typename base> struct Tree {
  // TYPES
  struct Leaf {
    base b;
  };

  struct Node {
    std::shared_ptr<List<Tree<base>>> kids;
  };

  using variant_t = std::variant<Leaf, Node>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Tree() {}

  explicit Tree(Leaf _v) : v_(std::move(_v)) {}

  explicit Tree(Node _v) : v_(std::move(_v)) {}

  template <typename CraneU>
  Tree(const Tree<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename Tree<CraneU>::Leaf>(_other.v())) {
            const auto &[b] = std::get<typename Tree<CraneU>::Leaf>(_other.v());
            return Leaf{[&]() -> base {
              if constexpr (crane_convertible<base, const CraneU &>) {
                return crane_convert<base>(b);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            const auto &[kids] =
                std::get<typename Tree<CraneU>::Node>(_other.v());
            return Node{(kids ? std::make_shared<List<Tree<base>>>(
                                    crane_convert<List<Tree<base>>>(*kids))
                              : nullptr)};
          }
        }()) {}

  static Tree<base> leaf(base b) { return Tree<base>(Leaf{std::move(b)}); }

  static Tree<base> node(List<Tree<base>> kids) {
    return Tree<base>(
        Node{std::make_shared<List<Tree<base>>>(std::move(kids))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Denote {
  template <Monad _tcI0, typename T2>
  static typename _tcI0::template m<T2> ret(const T2 &x);
  template <Monad _tcI0, typename T2, typename T3, typename F1>
  static typename _tcI0::template m<T3> bind(typename _tcI0::template m<T2> x,
                                             F1 &&x0);
  template <Monad _tcI0, typename T2, typename T3>
  static typename _tcI0::template m<List<T3>> map_monad(
      std::type_identity_t<crane::fn<typename _tcI0::template m<T3>(T2)>> f,
      const List<T2> &l);
  template <typename _tcI0, typename _tcI1, typename _tcI2, typename _tcI3,
            Params _tcI4, typename T1>
    requires C4<_tcI0, T1> && C3<_tcI1, T1> && C2<_tcI2, T1> && C1<_tcI3, T1>
  static std::optional<Tree<typename _tcI4::base>>
  freeze(const Tree<typename _tcI4::base> &t);
};

struct option_monad {
  template <typename CraneA0> using m = std::optional<CraneA0>;

  template <typename CraneA0> static std::optional<CraneA0> ret(CraneA0 x) {
    return std::make_optional<CraneA0>(std::move(x));
  }

  template <typename CraneA0, typename CraneA1>
  static std::optional<CraneA1>
  bind(std::optional<CraneA0> o, crane::fn<std::optional<CraneA1>(CraneA0)> f) {
    if (o.has_value()) {
      const CraneA0 &x = *o;
      return f(x);
    } else {
      return std::optional<CraneA1>();
    }
  }
};

static_assert(Monad<option_monad>);

struct nat_params {
  using base = Nat;

  static Nat base_default() { return Nat::o(); }
};

static_assert(Params<nat_params>);

struct c1n {
  static Nat c1(Nat x) { return x; }
};

static_assert(C1<c1n, Nat>);

struct c2n {
  static Nat c2(Nat x) { return x; }
};

static_assert(C2<c2n, Nat>);

struct c3n {
  static Nat c3(Nat x) { return x; }
};

static_assert(C3<c3n, Nat>);

struct c4n {
  static Nat c4(Nat x) { return x; }
};

static_assert(C4<c4n, Nat>);
std::optional<Tree<typename nat_params::base>>
go(const Tree<typename nat_params::base> &t);

template <Monad _tcI0, typename T2>
typename _tcI0::template m<T2> Denote::ret(const T2 &x) {
  return _tcI0::template ret<T2>(x);
}

template <Monad _tcI0, typename T2, typename T3, typename F1>
typename _tcI0::template m<T3> Denote::bind(typename _tcI0::template m<T2> x,
                                            F1 &&x0) {
  return _tcI0::template bind<T2, T3>(std::move(x), x0);
}

template <Monad _tcI0, typename T2, typename T3>
typename _tcI0::template m<List<T3>> Denote::map_monad(
    std::type_identity_t<crane::fn<typename _tcI0::template m<T3>(T2)>> f,
    const List<T2> &l) {
  if (std::holds_alternative<typename List<T2>::Nil>(l.v())) {
    return Denote::template ret<_tcI0, List<T3>>(List<T3>::nil());
  } else {
    const auto &[a0, a1] = std::get<typename List<T2>::Cons>(l.v());
    const List<T2> &a1_value = *a1;
    return Denote::template bind<_tcI0, T3, List<T3>>(f(a0), [=](const T3 &y) {
      return Denote::template bind<_tcI0, List<T3>, List<T3>>(
          Denote::template map_monad<_tcI0, T2, T3>(f, a1_value),
          [=](const List<T3> &ys) {
            return Denote::template ret<_tcI0, List<T3>>(List<T3>::cons(y, ys));
          });
    });
  }
}

template <typename _tcI0, typename _tcI1, typename _tcI2, typename _tcI3,
          Params _tcI4, typename T1>
  requires C4<_tcI0, T1> && C3<_tcI1, T1> && C2<_tcI2, T1> && C1<_tcI3, T1>
std::optional<Tree<typename _tcI4::base>>
Denote::freeze(const Tree<typename _tcI4::base> &t) {
  if (std::holds_alternative<typename Tree<typename _tcI4::base>::Leaf>(
          t.v())) {
    const auto &[b0] =
        std::get<typename Tree<typename _tcI4::base>::Leaf>(t.v());
    return Denote::template ret<option_monad, Tree<typename _tcI4::base>>(
        Tree<typename _tcI4::base>::leaf(b0));
  } else {
    const auto &[kids0] =
        std::get<typename Tree<typename _tcI4::base>::Node>(t.v());
    const List<Tree<typename _tcI4::base>> &kids0_value = *kids0;
    return Denote::template bind<option_monad, List<Tree<typename _tcI4::base>>,
                                 Tree<typename _tcI4::base>>(
        Denote::template map_monad<option_monad, Tree<typename _tcI4::base>,
                                   Tree<typename _tcI4::base>>(
            [](const Tree<typename _tcI4::base> &x) {
              return Denote::template freeze<_tcI0, _tcI1, _tcI2, _tcI3, _tcI4,
                                             T1>(x);
            },
            kids0_value),
        [](const List<Tree<typename _tcI4::base>> &ks) {
          return Denote::template ret<option_monad, Tree<typename _tcI4::base>>(
              Tree<typename _tcI4::base>::node(ks));
        });
  }
}

#endif // INCLUDED_POINT_FREE_FIX_BINDER_UNTYPED
