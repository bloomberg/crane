#ifndef INCLUDED_POINT_FREE_FIX_BINDER_UNTYPED
#define INCLUDED_POINT_FREE_FIX_BINDER_UNTYPED

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <functional>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct option_monad;
struct Nat;
template <typename A> struct List;
struct Tree;
struct nat_params;
struct c1n;
struct c2n;
struct c3n;
struct c4n;

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
    crane::small_vector<std::shared_ptr<Nat>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
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

  Nat(const Nat &) = default;
  Nat &operator=(const Nat &) = default;
  Nat(Nat &&) noexcept = default;
  Nat &operator=(Nat &&) noexcept = default;

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

  template <typename _U> List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ =
          Cons{[&]() -> A {
                 if constexpr (crane_convertible<A, const _U &>) {
                   return crane_convert<A>(a);
                 } else {
                   throw std::logic_error("unreachable: inactive constructor "
                                          "field at this instantiation");
                 }
               }(),
               (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                  : nullptr)};
    }
  }

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    crane::small_vector<std::shared_ptr<List<A>>> _stack = {};
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
        std::atomic_thread_fence(std::memory_order_acquire);
        _drain(_cur->v_mut());
      }
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename I>
concept Monad = requires {
  typename I::template m<std::any>;
  {
    I::template ret<std::any>(std::declval<std::any>())
  } -> std::convertible_to<typename I::template m<std::any>>;
  {
    I::template bind<std::any, std::any>(
        std::declval<typename I::template m<std::any>>(),
        std::declval<
            std::function<typename I::template m<std::any>(std::any)>>())
  } -> std::convertible_to<typename I::template m<std::any>>;
};
template <typename
I>concept Params = requires {
  typename I::base;
} && (requires {
  { I::base_default() } -> std::convertible_to<typename I::base>;
} || requires {
  { I::base_default } -> std::convertible_to<typename I::base>;
});
using base = std::any;
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

struct Tree {
  // TYPES
  struct Leaf {
    base b;
  };

  struct Node {
    std::shared_ptr<List<Tree>> kids;
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

  static Tree leaf(base b) { return Tree(Leaf{std::move(b)}); }

  static Tree node(List<Tree> kids) {
    return Tree(Node{std::make_shared<List<Tree>>(std::move(kids))});
  }

  // MANIPULATORS
  ~Tree() {
    crane::small_vector<std::shared_ptr<Tree>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Node>(&_v)) {
        if (_alt->kids && _alt->kids.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          auto _lp = _alt->kids.get();
          while (std::holds_alternative<typename List<Tree>::Cons>(_lp->v())) {
            auto &_lc = std::get<typename List<Tree>::Cons>(_lp->v_mut());
            _stack.push_back(std::make_shared<Tree>(std::move(_lc.a)));
            if (_lc.l && _lc.l.use_count() == 1) {
              std::atomic_thread_fence(std::memory_order_acquire);
              _lp = _lc.l.get();
            } else {
              break;
            }
          }
          _alt->kids.reset();
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

  Tree(const Tree &) = default;
  Tree &operator=(const Tree &) = default;
  Tree(Tree &&) noexcept = default;
  Tree &operator=(Tree &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Denote {
  template <Monad _tcI0, typename T2>
  static typename _tcI0::template m<T2> ret(const T2 &x);
  template <Monad _tcI0, typename T2, typename T3, typename F1>
    requires std::is_invocable_r_v<typename _tcI0::template m<T3>, F1 &, T2 &>
  static typename _tcI0::template m<T3> bind(typename _tcI0::template m<T2> x,
                                             F1 &&x0);
  template <Monad _tcI0, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<typename _tcI0::template m<T3>, F0 &, T2 &>
  static typename _tcI0::template m<List<T3>> map_monad(F0 &&f,
                                                        const List<T2> &l);
  template <typename _tcI0, typename _tcI1, typename _tcI2, typename _tcI3,
            Params _tcI4, typename T1>
    requires C4<_tcI0, T1> && C3<_tcI1, T1> && C2<_tcI2, T1> && C1<_tcI3, T1>
  static std::optional<Tree> freeze(const Tree &t);
};

struct option_monad {
  template <typename _A0> using m = std::optional<_A0>;

  template <typename _A0> static std::optional<_A0> ret(_A0 x) {
    return std::make_optional<_A0>(x);
  }

  template <typename _A0, typename _A1>
  static std::optional<_A1> bind(std::optional<_A0> o,
                                 std::function<std::optional<_A1>(_A0)> f) {
    if (o.has_value()) {
      const _A0 &x = *o;
      return f(x);
    } else {
      return std::optional<_A1>();
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
std::optional<Tree> go(const Tree &t);

template <Monad _tcI0, typename T2>
typename _tcI0::template m<T2> Denote::ret(const T2 &x) {
  return _tcI0::template ret<T2>(x);
}

template <Monad _tcI0, typename T2, typename T3, typename F1>
  requires std::is_invocable_r_v<typename _tcI0::template m<T3>, F1 &, T2 &>
typename _tcI0::template m<T3> Denote::bind(typename _tcI0::template m<T2> x,
                                            F1 &&x0) {
  return _tcI0::template bind<T2, T3>(std::move(x), x0);
}

template <Monad _tcI0, typename T2, typename T3, typename F0>
  requires std::is_invocable_r_v<typename _tcI0::template m<T3>, F0 &, T2 &>
typename _tcI0::template m<List<T3>> Denote::map_monad(F0 &&f,
                                                       const List<T2> &l) {
  if (std::holds_alternative<typename List<T2>::Nil>(l.v())) {
    return Denote::template ret<_tcI0, List<T3>>(List<T3>::nil());
  } else {
    const auto &[a0, a1] = std::get<typename List<T2>::Cons>(l.v());
    const List<T2> &a1_value = *a1;
    return Denote::template bind<_tcI0, T3, List<T3>>(f(a0), [=](T3 y) mutable {
      return Denote::template bind<_tcI0, List<T3>, List<T3>>(
          Denote::template map_monad<_tcI0, T2, T3>(f, a1_value),
          [=](const auto &ys) mutable {
            return Denote::template ret<_tcI0, List<T3>>(List<T3>::cons(y, ys));
          });
    });
  }
}

template <typename _tcI0, typename _tcI1, typename _tcI2, typename _tcI3,
          Params _tcI4, typename T1>
  requires C4<_tcI0, T1> && C3<_tcI1, T1> && C2<_tcI2, T1> && C1<_tcI3, T1>
std::optional<Tree> Denote::freeze(const Tree &t) {
  if (std::holds_alternative<typename Tree::Leaf>(t.v())) {
    const auto &[b0] = std::get<typename Tree::Leaf>(t.v());
    return Denote::template ret<option_monad, Tree>(Tree::leaf(b0));
  } else {
    const auto &[kids0] = std::get<typename Tree::Node>(t.v());
    const List<Tree> &kids0_value = *kids0;
    return Denote::template bind<option_monad, List<Tree>, Tree>(
        Denote::template map_monad<option_monad, Tree, Tree>(
            [](const Tree &x) {
              return Denote::template freeze<_tcI0, _tcI1, _tcI2, _tcI3, _tcI4,
                                             T1>(x);
            },
            kids0_value),
        [](List<Tree> ks) {
          return Denote::template ret<option_monad, Tree>(Tree::node(ks));
        });
  }
}

#endif // INCLUDED_POINT_FREE_FIX_BINDER_UNTYPED
