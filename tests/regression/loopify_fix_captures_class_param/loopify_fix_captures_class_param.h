#ifndef INCLUDED_LOOPIFY_FIX_CAPTURES_CLASS_PARAM
#define INCLUDED_LOOPIFY_FIX_CAPTURES_CLASS_PARAM

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct List;

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

  bool ltb(const Nat &m) const { return Nat::s(*this).leb(m); }

  bool leb(const Nat &m) const {
    const Nat *_loop_self = this;
    const Nat *_loop_m = &m;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        return true;
      } else {
        const auto &[a0] = std::get<typename Nat::S>(_sv.v());
        if (std::holds_alternative<typename Nat::O>(_loop_m->v())) {
          return false;
        } else {
          const auto &[a00] = std::get<typename Nat::S>(_loop_m->v());
          _loop_self = crane_raw(a0);
          _loop_m = crane_raw(a00);
        }
      }
    }
  }

  Nat sub(const Nat &m) const {
    const Nat *_loop_self = this;
    const Nat *_loop_m = &m;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        return *_loop_self;
      } else {
        const auto &[a0] = std::get<typename Nat::S>(_sv.v());
        if (std::holds_alternative<typename Nat::O>(_loop_m->v())) {
          return *_loop_self;
        } else {
          const auto &[a00] = std::get<typename Nat::S>(_loop_m->v());
          _loop_self = crane_raw(a0);
          _loop_m = crane_raw(a00);
        }
      }
    }
  }

  Nat add(Nat m) const {
    std::optional<Nat> _root{};
    std::shared_ptr<Nat> *_write = nullptr;
    const Nat *_loop_self = this;
    Nat _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        auto _value = std::move(_loop_m);
        (_write ? *(*_write = std::make_shared<Nat>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0] = std::get<typename Nat::S>(_sv.v());
        auto _cell = typename Nat::S(nullptr);
        Nat &_node =
            (_write ? *(*_write = std::make_shared<Nat>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename Nat::S>(_node.v_mut()).a0;
        _loop_self = crane_raw(a0);
        continue;
      }
    }
    return std::move(*_root);
  }
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
};

template <typename I>
concept Sized = requires {
  { I::size(std::declval<Nat>()) } -> std::convertible_to<Nat>;
};

struct LoopifyFixCapturesClassParam {
  struct tree {
    // TYPES
    struct Leaf {
      Nat n;
    };

    struct Node {
      std::shared_ptr<List<tree>> ts;
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

    static tree leaf(Nat n) { return tree(Leaf{std::move(n)}); }

    static tree node(List<tree> ts) {
      return tree(Node{std::make_shared<List<tree>>(std::move(ts))});
    }

    // MANIPULATORS
    ~tree() {
      if (std::holds_alternative<Leaf>(v_mut())) {
        return;
      }
      crane::small_vector<std::shared_ptr<tree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->ts && _alt->ts.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            auto _lp = _alt->ts.get();
            while (
                std::holds_alternative<typename List<tree>::Cons>(_lp->v())) {
              auto &_lc = std::get<typename List<tree>::Cons>(_lp->v_mut());
              _stack.push_back(std::make_shared<tree>(std::move(_lc.a)));
              if (_lc.l && _lc.l.use_count() == 1) {
                std::atomic_thread_fence(std::memory_order_acquire);
                _lp = _lc.l.get();
              } else {
                break;
              }
            }
            _alt->ts.reset();
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

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, const Nat &>
  static T1 tree_rect(F0 &&f0, F1 &&f1, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      const auto &[n0] = std::get<typename tree::Leaf>(t.v());
      return f0(n0);
    } else {
      const auto &[ts0] = std::get<typename tree::Node>(t.v());
      return f1(*ts0);
    }
  }

  template <typename T1, typename F0, typename F1>
  static T1 tree_rec(F0 &&f0, F1 &&f1, const tree &t) {
    return tree_rect<T1>(f0, f1, t);
  }

  template <Sized _tcI0>
  static std::optional<Nat> f(const tree &t,
                              Nat i) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

    struct CraneEnter {
      Nat i;
      tree t;
    };

    /// CraneEnter_loop: captures varying parameters for each recursive call.
    struct CraneEnter_loop {
      Nat k;
      List<tree> ts;
    };

    using CraneFrame = std::variant<CraneEnter, CraneEnter_loop>;
    std::optional<Nat> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{std::move(i), t});
    /// Loopified f: CraneEnter.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        Nat i = std::move(_f.i);
        const tree &t = std::move(_f.t);
        if (std::holds_alternative<typename tree::Leaf>(t.v())) {
          const auto &[n0] = std::get<typename tree::Leaf>(t.v());
          _result = std::make_optional<Nat>(n0.add(std::move(i)));
        } else {
          const auto &[ts0] = std::get<typename tree::Node>(t.v());
          _stack.emplace_back(CraneEnter_loop{std::move(i), *ts0});
        }
      } else {
        auto _f = std::move(std::get<CraneEnter_loop>(_frame));
        Nat k = std::move(_f.k);
        const List<tree> &ts = std::move(_f.ts);
        if (std::holds_alternative<typename List<tree>::Nil>(ts.v())) {
          _result = std::optional<Nat>();
        } else {
          const auto &[a0, a1] = std::get<typename List<tree>::Cons>(ts.v());
          if (k.ltb(_tcI0::size(Nat::s(Nat::s(Nat::o()))))) {
            _stack.emplace_back(CraneEnter{std::move(k), a0});
          } else {
            _stack.emplace_back(CraneEnter_loop{
                std::move(k).sub(_tcI0::size(Nat::s(Nat::s(Nat::o())))), *a1});
          }
        }
      }
    }
    return _result;
  }

  struct id_size {
    static Nat size(Nat n) { return n; }
  };

  static_assert(Sized<id_size>);
  static inline const std::optional<Nat> result = f<id_size>(
      tree::node(List<tree>::cons(
          tree::leaf(Nat::s(Nat::o())),
          List<tree>::cons(
              tree::node(List<tree>::cons(
                  tree::leaf(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))))),
                  List<tree>::nil())),
              List<tree>::nil()))),
      Nat::s(Nat::s(Nat::s(Nat::o()))));
};

#endif // INCLUDED_LOOPIFY_FIX_CAPTURES_CLASS_PARAM
