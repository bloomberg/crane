#pragma once

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
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

  static List<A> cons(A a, crane::shared_child_slot<List<A>> l) {
    return List<A>(Cons{std::move(a), l.take()});
  }

  // MANIPULATORS
  ~List() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
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
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
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

struct SigIsItsWitness {
  /// A plain witness, built, projected and matched.
  static uint64_t pos(uint64_t n);
  static uint64_t pos_val(uint64_t n);
  static uint64_t pos_match(uint64_t n);
  /// Nested: a sig of a sig.
  static uint64_t nested(uint64_t n);
  static uint64_t nested_val(uint64_t n);
  /// A function as the witness.
  [[gnu::used]] static inline const crane::fn<uint64_t(uint64_t)> fixes_zero =
      [](uint64_t x) { return (x * UINT64_C(2)); };
  static uint64_t apply_fixes_zero(uint64_t n);
  /// unit as the witness.
  static constexpr std::monostate unit_sig = std::monostate{};
  static uint64_t unit_sig_used(uint64_t n);

  /// A type variable as the witness.
  template <typename T1> static T1 wrap(const T1 &x) { return x; }

  static List<uint64_t> unwrap_list(const List<uint64_t> &xs);
  /// Witnesses in a container.
  static List<uint64_t> positives(uint64_t k);
  static uint64_t sum_positives(uint64_t k);

  /// A recursive inductive whose constructor holds a sig of itself.
  struct rt {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<rt> a0;
      uint64_t a1;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    rt() {}

    explicit rt(Leaf _v) : v_(_v) {}

    explicit rt(Node _v) : v_(std::move(_v)) {}

    static rt leaf() { return rt(Leaf{}); }

    static rt node(rt a0, uint64_t a1) {
      return rt(Node{std::make_shared<rt>(std::move(a0)), a1});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
  static T1 rt_rect(T1 f, F1 &&f0, const rt &r) {
    if (std::holds_alternative<typename rt::Leaf>(r.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename rt::Node>(r.v());
      return f0(*a0, a1);
    }
  }

  template <typename T1, typename F1>
  static T1 rt_rec(T1 f, F1 &&f0, const rt &r) {
    return rt_rect<T1>(std::move(f), f0, r);
  }

  static uint64_t rt_sum(const rt &t);
  static inline const rt rt_example =
      rt::node(rt::node(rt::leaf(), UINT64_C(3)), UINT64_C(4));
  static inline const uint64_t rt_example_sum = rt_sum(rt_example);
  /// sig2.
  static uint64_t between(uint64_t n);
  static uint64_t between_val(uint64_t n);
};
