#ifndef INCLUDED_LOOPIFY_TOP_LEVEL_CALL_BINDING
#define INCLUDED_LOOPIFY_TOP_LEVEL_CALL_BINDING

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

/// A recursive call bound at the top of a function's body, the rest of
/// the body after it.
///
/// csum's body matches nothing: it adds key c to a local fixpoint
/// applied to kids c, which Normalize binds first.  The machine adopts
/// the fixpoint, which calls back into csum, and reroutes the bound call
/// to it.  The machine rewrote its body one top-level statement at a time,
/// so the binding never resumed into the addition after it, and the
/// rerouted call was left naming the entry, which is no function.
struct LoopifyTopLevelCallBinding {
  struct cell {
    // TYPES
    struct MkCell {
      uint64_t key;
      std::shared_ptr<List<cell>> kids;
    };

    using variant_t = std::variant<MkCell>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    cell() {}

    explicit cell(MkCell _v) : v_(std::move(_v)) {}

    static cell mkcell(uint64_t key, List<cell> kids) {
      return cell(MkCell{key, std::make_shared<List<cell>>(std::move(kids))});
    }

    // MANIPULATORS
    ~cell() {
      crane::small_vector<std::shared_ptr<cell>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<MkCell>(&_v)) {
          if (_alt->kids && _alt->kids.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            auto _lp = _alt->kids.get();
            while (
                std::holds_alternative<typename List<cell>::Cons>(_lp->v())) {
              auto &_lc = std::get<typename List<cell>::Cons>(_lp->v_mut());
              _stack.push_back(std::make_shared<cell>(std::move(_lc.a)));
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

    cell(const cell &) = default;
    cell &operator=(const cell &) = default;
    cell(cell &&) = default;
    cell &operator=(cell &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0>
  static T1 cell_rect(F0 &&f, const cell &c) {
    const auto &[key1, kids1] = std::get<typename cell::MkCell>(c.v());
    return f(key1, *kids1);
  }

  template <typename T1, typename F0>
  static T1 cell_rec(F0 &&f, const cell &c) {
    return cell_rect<T1>(f, c);
  }

  static uint64_t key(const cell &c);
  static List<cell> kids(const cell &c);
  static uint64_t csum(const cell &c);
  /// A chain n cells deep, each holding k.
  static cell chain(uint64_t n, uint64_t k);
  static inline const cell wide = cell::mkcell(
      UINT64_C(1),
      List<cell>::cons(
          cell::mkcell(UINT64_C(2), List<cell>::nil()),
          List<cell>::cons(
              cell::mkcell(
                  UINT64_C(3),
                  List<cell>::cons(cell::mkcell(UINT64_C(4), List<cell>::nil()),
                                   List<cell>::nil())),
              List<cell>::nil())));
};

#endif // INCLUDED_LOOPIFY_TOP_LEVEL_CALL_BINDING
