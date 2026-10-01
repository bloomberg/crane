#ifndef INCLUDED_EXPANDED_PRODUCT_WRONG_CLASS_FIELD
#define INCLUDED_EXPANDED_PRODUCT_WRONG_CLASS_FIELD

#include "crane_fn.h"
#include "obj.h"
#include <any>
#include <atomic>
#include <concepts>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A> struct List;
template <typename provenance, typename allocationId, typename ptr>
struct state;
using provenance = crane::obj;
using allocationId = crane::obj;
using ptr = crane::obj;
template <typename
I>concept Prov = requires {
  typename I::provenance;
  typename I::allocationId;
  typename I::prov;
} && (requires {
  { I::no_prov() } -> std::convertible_to<typename I::prov>;
} || requires {
  { I::no_prov } -> std::convertible_to<typename I::prov>;
}) && (requires {
  { I::a_provenance() } -> std::convertible_to<typename I::provenance>;
} || requires {
  { I::a_provenance } -> std::convertible_to<typename I::provenance>;
}) && (requires {
  { I::an_allocationId() } -> std::convertible_to<typename I::allocationId>;
} || requires {
  { I::an_allocationId } -> std::convertible_to<typename I::allocationId>;
});
template <typename
I>concept Ptr = requires {
  typename I::ptr;
} && (requires {
  { I::zero_ptr() } -> std::convertible_to<typename I::ptr>;
} || requires {
  { I::zero_ptr } -> std::convertible_to<typename I::ptr>;
});
/// The fields are themselves instances: the wrong spelling in Vellvm is
/// typename _tcI0::PROV::prov, a sibling field of an {e inner} class.
template <typename I>
concept ParamsV = requires {
  typename I::PROV;
  typename I::PTR;
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

  template <typename _U>
  List(const List<_U> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
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
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename provenance, typename allocationId, typename ptr>
struct state {
  provenance st_prov;
  allocationId st_alloc;
  ptr st_ptr;
};

template <typename ptr> using frame = List<ptr>;
template <typename provenance, typename allocationId, typename ptr>
using fused = std::pair<state<provenance, allocationId, ptr>, frame<ptr>>;

/// Reads the expanded product, so the caller's parameter is inferred at it
/// rather than at the alias.
template <ParamsV _tcI0>
typename _tcI0::PTR::ptr
top(const std::pair<
    state<typename _tcI0::PROV::provenance, typename _tcI0::PROV::allocationId,
          typename _tcI0::PTR::ptr>,
    List<typename _tcI0::PTR::ptr>> &p) {
  return p.first.st_ptr;
}

/// s is unannotated: Rocq infers it from top's domain.  The return type
/// still names fused.
template <ParamsV _tcI0>
fused<typename _tcI0::PROV::provenance, typename _tcI0::PROV::allocationId,
      typename _tcI0::PTR::ptr>
step(const std::pair<
     state<typename _tcI0::PROV::provenance, typename _tcI0::PROV::allocationId,
           typename _tcI0::PTR::ptr>,
     List<typename _tcI0::PTR::ptr>> &s) {
  return std::make_pair(s.first, s.second);
}

template <ParamsV _tcI0>
fused<typename _tcI0::PROV::provenance, typename _tcI0::PROV::allocationId,
      typename _tcI0::PTR::ptr>
initial() {
  return std::make_pair(
      state<typename _tcI0::PROV::provenance,
            typename _tcI0::PROV::allocationId, typename _tcI0::PTR::ptr>{
          _tcI0::PROV::a_provenance(), _tcI0::PROV::an_allocationId(),
          _tcI0::PTR::zero_ptr()},
      List<typename _tcI0::PTR::ptr>::nil());
}

struct ExpandedProductWrongClassField {
  template <ParamsV _tcI0> static typename _tcI0::PTR::ptr use() {
    return top<_tcI0>(step<_tcI0>(initial<_tcI0>()));
  }
};

#endif // INCLUDED_EXPANDED_PRODUCT_WRONG_CLASS_FIELD
