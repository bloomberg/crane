#ifndef INCLUDED_LOOPIFY_ADOPTED_FIX_NAME_SHARED
#define INCLUDED_LOOPIFY_ADOPTED_FIX_NAME_SHARED

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
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

/// Crane bug (compile error): under Set Crane Loopify, a function whose
/// body let-binds two local fixpoints of the same name -- both loop, the
/// first inside a lambda -- adopts one as a second machine entry, and
/// installing the adoption reroutes calls by name.  The names are shared
/// (loop_impl, loop, _self_loop), so the other fixpoint's calls were
/// rerouted too, to an entry that never handles them:
/// error: use of undeclared identifier '_adopted_loop'
///
/// Reduced from Vellvm, Semantics/MemoryBytes.v:112
/// (dvalue_extract_byte: dvalue_extract_struct_bytes under its pad
/// lambda, and dvalue_extract_array_bytes).
struct LoopifyAdoptedFixNameShared {
  struct tree {
    // TYPES
    struct Leaf {
      Nat n;
    };

    struct Node {
      std::shared_ptr<List<tree>> ts;
    };

    struct Arr {
      std::shared_ptr<List<tree>> ts;
    };

    using variant_t = std::variant<Leaf, Node, Arr>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Leaf _v) : v_(std::move(_v)) {}

    explicit tree(Node _v) : v_(std::move(_v)) {}

    explicit tree(Arr _v) : v_(std::move(_v)) {}

    static tree leaf(Nat n) { return tree(Leaf{std::move(n)}); }

    static tree node(List<tree> ts) {
      return tree(Node{std::make_shared<List<tree>>(std::move(ts))});
    }

    static tree arr(List<tree> ts) {
      return tree(Arr{std::make_shared<List<tree>>(std::move(ts))});
    }

    // MANIPULATORS
    ~tree() {
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
        if (auto *_alt = std::get_if<Arr>(&_v)) {
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

  template <typename T1, typename F0, typename F1, typename F2>
    requires std::is_invocable_r_v<T1, F0 &, const Nat &>
  static T1 tree_rect(F0 &&f0, F1 &&f1, F2 &&f2, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      const auto &[n0] = std::get<typename tree::Leaf>(t.v());
      return f0(n0);
    } else if (std::holds_alternative<typename tree::Node>(t.v())) {
      const auto &[ts0] = std::get<typename tree::Node>(t.v());
      return f1(*ts0);
    } else {
      const auto &[ts0] = std::get<typename tree::Arr>(t.v());
      return f2(*ts0);
    }
  }

  template <typename T1, typename F0, typename F1, typename F2>
    requires std::is_invocable_r_v<T1, F0 &, const Nat &>
  static T1 tree_rec(F0 &&f0, F1 &&f1, F2 &&f2, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      const auto &[n0] = std::get<typename tree::Leaf>(t.v());
      return f0(n0);
    } else if (std::holds_alternative<typename tree::Node>(t.v())) {
      const auto &[ts0] = std::get<typename tree::Node>(t.v());
      return f1(*ts0);
    } else {
      const auto &[ts0] = std::get<typename tree::Arr>(t.v());
      return f2(*ts0);
    }
  }

  static std::optional<Nat> f(const tree &t, const Nat &i);
  /// The struct loop skips Leaf 1 (4 >= 3), enters the array at 1, and
  /// the array loop reaches Leaf 7 at 1.
  static inline const std::optional<Nat> r1 =
      f(tree::node(List<tree>::cons(
            tree::leaf(Nat::s(Nat::o())),
            List<tree>::cons(
                tree::arr(List<tree>::cons(
                    tree::leaf(Nat::s(Nat::s(
                        Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))))))),
                    List<tree>::cons(tree::leaf(Nat::s(Nat::s(
                                         Nat::s(Nat::s(Nat::s(Nat::o())))))),
                                     List<tree>::nil()))),
                List<tree>::nil()))),
        Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))));
};

#endif // INCLUDED_LOOPIFY_ADOPTED_FIX_NAME_SHARED
