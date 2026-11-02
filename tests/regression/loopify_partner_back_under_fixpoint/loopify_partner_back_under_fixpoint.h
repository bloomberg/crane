#ifndef INCLUDED_LOOPIFY_PARTNER_BACK_UNDER_FIXPOINT
#define INCLUDED_LOOPIFY_PARTNER_BACK_UNDER_FIXPOINT

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
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
};

/// tree_size's partner forest_size calls it back only from a local
/// fixpoint over a list of trees, and tree_size calls forest_size as
/// the operand of an addition.  No machine can enter forest_size, so its
/// body is spliced in place of the call.  The addition is then copied into
/// the one branch of the match the body is, which applies the local
/// fixpoint where tree_size's machine runs it as a loop of its own: the
/// calls of tree_size in it are turns, and a chain of any depth runs in
/// one C++ frame.
struct LoopifyPartnerBackUnderFixpoint {
  struct tree;
  struct forest;

  struct tree {
    // TYPES
    struct Node {
      uint64_t n;
      std::shared_ptr<forest> kids;
    };

    using variant_t = std::variant<Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Node _v) : v_(std::move(_v)) {}

    static tree node(uint64_t n, forest kids) {
      return tree(Node{n, std::make_shared<forest>(std::move(kids))});
    }

    // MANIPULATORS
    ~tree() {
      crane::small_vector<crane::obj> _stack = {};
      auto _drain_self = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->kids && _alt->kids.use_count() == 1) {
            _stack.push_back(std::move(_alt->kids));
          }
        }
      };
      _drain_self(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (auto *_sp = crane::any_cast<std::shared_ptr<tree>>(&_cur)) {
          if (*_sp && (*_sp).use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            _drain_self((*_sp)->v_mut());
          }
        } else {
          if (auto *_sp = crane::any_cast<std::shared_ptr<forest>>(&_cur)) {
            if (*_sp && (*_sp).use_count() == 1) {
              auto &_pv = (*_sp)->v_mut();
              if (auto *_alt = std::get_if<typename forest::Forest0>(&_pv)) {
                if (_alt->ts && _alt->ts.use_count() == 1) {
                  std::atomic_thread_fence(std::memory_order_acquire);
                  auto _lp = _alt->ts.get();
                  while (std::holds_alternative<typename List<tree>::Cons>(
                      _lp->v())) {
                    auto &_lc =
                        std::get<typename List<tree>::Cons>(_lp->v_mut());
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
            }
          }
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

  struct forest {
    // TYPES
    struct Forest0 {
      std::shared_ptr<List<tree>> ts;
    };

    using variant_t = std::variant<Forest0>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    forest() {}

    explicit forest(Forest0 _v) : v_(std::move(_v)) {}

    static forest forest0(List<tree> ts) {
      return forest(Forest0{std::make_shared<List<tree>>(std::move(ts))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0>
  static T1 tree_rect(F0 &&f, const tree &t) {
    const auto &[n0, kids0] = std::get<typename tree::Node>(t.v());
    return f(n0, *kids0);
  }

  template <typename T1, typename F0>
  static T1 tree_rec(F0 &&f, const tree &t) {
    return tree_rect<T1>(f, t);
  }

  template <typename T1, typename F0>
  static T1 forest_rect(F0 &&f, const forest &f0) {
    const auto &[ts0] = std::get<typename forest::Forest0>(f0.v());
    return f(*ts0);
  }

  template <typename T1, typename F0>
  static T1 forest_rec(F0 &&f, const forest &f0) {
    return forest_rect<T1>(f, f0);
  }

  static uint64_t tree_size(const tree &t);
  static uint64_t forest_size(const forest &f);
  static tree chain(uint64_t k, tree t);
};

#endif // INCLUDED_LOOPIFY_PARTNER_BACK_UNDER_FIXPOINT
