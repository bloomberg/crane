#ifndef INCLUDED_MODULE_TYPE_MENTIONS_OUTER_RECORD
#define INCLUDED_MODULE_TYPE_MENTIONS_OUTER_RECORD

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;

struct Nat {};

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

struct ModuleTypeMentionsOuterRecord {
  template <typename A> struct ops {
    crane::fn<A(A, A)> plus;
    A zero;

    // ACCESSORS
    template <typename CraneU> operator ops<CraneU>() const {
      return {crane_convert<crane::fn<CraneU(CraneU, CraneU)>>(plus),
              [&]() -> CraneU {
                if constexpr (crane_convertible<CraneU, const A &>) {
                  return crane_convert<CraneU>(zero);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }()};
    }
  };

  struct NatT {
    using t = uint64_t;
    static inline const ops<uint64_t> o = ops<uint64_t>{
        [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); },
        UINT64_C(0)};
  };

  template <typename X> struct Use {
    static typename X::t sum(const List<typename X::t> &l) {
      return l.template fold_left<typename X::t>(X::o.plus, X::o.zero);
    }
  };

  using U = Use<NatT>;
  static inline const uint64_t result = U::sum(List<uint64_t>::cons(
      UINT64_C(1), List<uint64_t>::cons(
                       UINT64_C(2), List<uint64_t>::cons(
                                        UINT64_C(3), List<uint64_t>::nil()))));
};

template <typename M>
concept T = requires {
  typename M::t;
  requires(
      requires {
        {
          M::o
        } -> std::convertible_to<
            ModuleTypeMentionsOuterRecord::ops<typename M::t>>;
      } ||
      requires {
        {
          M::o()
        } -> std::convertible_to<
            ModuleTypeMentionsOuterRecord::ops<typename M::t>>;
      });
};

#endif // INCLUDED_MODULE_TYPE_MENTIONS_OUTER_RECORD
