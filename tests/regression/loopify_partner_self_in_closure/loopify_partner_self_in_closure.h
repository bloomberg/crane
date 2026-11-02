#ifndef INCLUDED_LOOPIFY_PARTNER_SELF_IN_CLOSURE
#define INCLUDED_LOOPIFY_PARTNER_SELF_IN_CLOSURE

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
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
    requires std::is_invocable_r_v<T1, F0 &, T1 &&, const A &>
  T1 fold_left(F0 &&f, T1 a0) const {
    const List<A> *_loop_self = this;
    T1 _loop_a0 = std::move(a0);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        return _loop_a0;
      } else {
        const auto &[a1, a2] = std::get<typename List<A>::Cons>(_sv.v());
        _loop_self = crane_raw(a2);
        _loop_a0 = f(std::move(_loop_a0), a1);
      }
    }
  }
};

/// sum_e calls its partner sum_md as an operand, and sum_md calls
/// sum_e back, so sum_e's machine would enter a copy of sum_md -- but
/// sum_md also calls itself inside the closure it folds a list with, and
/// the copy a machine enters is no value a closure could call.  Its body
/// runs in place of the call instead.
struct LoopifyPartnerSelfInClosure {
  struct e;
  struct md;

  struct e {
    // TYPES
    struct Leaf {
      uint64_t n;
    };

    struct Meta {
      std::shared_ptr<md> m;
    };

    using variant_t = std::variant<Leaf, Meta>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    e() {}

    explicit e(Leaf _v) : v_(std::move(_v)) {}

    explicit e(Meta _v) : v_(std::move(_v)) {}

    static e leaf(uint64_t n) { return e(Leaf{n}); }

    static e meta(md m) { return e(Meta{std::make_shared<md>(std::move(m))}); }

    // MANIPULATORS
    ~e() {
      crane::small_vector<crane::obj> _stack = {};
      auto _drain_self = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Meta>(&_v)) {
          if (_alt->m && _alt->m.use_count() == 1) {
            _stack.push_back(std::move(_alt->m));
          }
        }
      };
      _drain_self(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (auto *_sp = crane::any_cast<std::shared_ptr<e>>(&_cur)) {
          if (*_sp && (*_sp).use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            _drain_self((*_sp)->v_mut());
          }
        } else {
          if (auto *_sp = crane::any_cast<std::shared_ptr<md>>(&_cur)) {
            if (*_sp && (*_sp).use_count() == 1) {
              auto &_pv = (*_sp)->v_mut();
              if (auto *_alt = std::get_if<typename md::MConst>(&_pv)) {
                if (_alt->x && _alt->x.use_count() == 1) {
                  _stack.push_back(std::move(_alt->x));
                }
              }
            }
          }
        }
      }
    }

    e(const e &) = default;
    e &operator=(const e &) = default;
    e(e &&) = default;
    e &operator=(e &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  struct md {
    // TYPES
    struct MNil {};

    struct MNode {
      std::shared_ptr<List<md>> l;
    };

    struct MConst {
      std::shared_ptr<e> x;
    };

    using variant_t = std::variant<MNil, MNode, MConst>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    md() {}

    explicit md(MNil _v) : v_(_v) {}

    explicit md(MNode _v) : v_(std::move(_v)) {}

    explicit md(MConst _v) : v_(std::move(_v)) {}

    static md mnil() { return md(MNil{}); }

    static md mnode(List<md> l) {
      return md(MNode{std::make_shared<List<md>>(std::move(l))});
    }

    static md mconst(e x) {
      return md(MConst{std::make_shared<e>(std::move(x))});
    }

    // MANIPULATORS
    ~md() {
      crane::small_vector<crane::obj> _stack = {};
      auto _drain_self = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<MNode>(&_v)) {
          if (_alt->l && _alt->l.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            auto _lp = _alt->l.get();
            while (std::holds_alternative<typename List<md>::Cons>(_lp->v())) {
              auto &_lc = std::get<typename List<md>::Cons>(_lp->v_mut());
              _stack.push_back(std::make_shared<md>(std::move(_lc.a)));
              if (_lc.l && _lc.l.use_count() == 1) {
                std::atomic_thread_fence(std::memory_order_acquire);
                _lp = _lc.l.get();
              } else {
                break;
              }
            }
            _alt->l.reset();
          }
        }
        if (auto *_alt = std::get_if<MConst>(&_v)) {
          if (_alt->x && _alt->x.use_count() == 1) {
            _stack.push_back(std::move(_alt->x));
          }
        }
      };
      _drain_self(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (auto *_sp = crane::any_cast<std::shared_ptr<md>>(&_cur)) {
          if (*_sp && (*_sp).use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            _drain_self((*_sp)->v_mut());
          }
        } else {
          if (auto *_sp = crane::any_cast<std::shared_ptr<e>>(&_cur)) {
            if (*_sp && (*_sp).use_count() == 1) {
              auto &_pv = (*_sp)->v_mut();
              if (auto *_alt = std::get_if<typename e::Meta>(&_pv)) {
                if (_alt->m && _alt->m.use_count() == 1) {
                  _stack.push_back(std::move(_alt->m));
                }
              }
            }
          }
        }
      }
    }

    md(const md &) = default;
    md &operator=(const md &) = default;
    md(md &&) = default;
    md &operator=(md &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
  static T1 e_rect(F0 &&f, F1 &&f0, const e &e0) {
    if (std::holds_alternative<typename e::Leaf>(e0.v())) {
      const auto &[n0] = std::get<typename e::Leaf>(e0.v());
      return f(n0);
    } else {
      const auto &[m0] = std::get<typename e::Meta>(e0.v());
      return f0(*m0);
    }
  }

  template <typename T1, typename F0, typename F1>
  static T1 e_rec(F0 &&f, F1 &&f0, const e &e0) {
    return e_rect<T1>(f, f0, e0);
  }

  template <typename T1, typename F1, typename F2>
  static T1 md_rect(T1 f, F1 &&f0, F2 &&f1, const md &m) {
    if (std::holds_alternative<typename md::MNil>(m.v())) {
      return f;
    } else if (std::holds_alternative<typename md::MNode>(m.v())) {
      const auto &[l0] = std::get<typename md::MNode>(m.v());
      return f0(*l0);
    } else {
      const auto &[x0] = std::get<typename md::MConst>(m.v());
      return f1(*x0);
    }
  }

  template <typename T1, typename F1, typename F2>
  static T1 md_rec(T1 f, F1 &&f0, F2 &&f1, const md &m) {
    return md_rect<T1>(std::move(f), f0, f1, m);
  }

  static uint64_t sum_e(const e &x);
  static uint64_t sum_md(const md &m);
  /// 1 + (2 + (1 + 3))
  static bool check(std::monostate _x);
};

#endif // INCLUDED_LOOPIFY_PARTNER_SELF_IN_CLOSURE
