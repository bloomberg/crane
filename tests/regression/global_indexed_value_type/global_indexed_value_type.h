#pragma once

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <crane_itree.h>
#include <crane_st.h>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <span>
#include <stdexcept>
#include <string>
#include <string_view>
#include <utility>
#include <variant>

struct nat_ref_class;
template <typename A> struct List;
template <typename Err> struct ExceptE;
struct Err;
struct NatRef;
template <typename I, typename T>
concept RefClass = requires {
  { I::make_ref(std::declval<T>()) } -> std::convertible_to<crane::obj>;
  { I::ref_index(std::declval<crane::obj>()) } -> std::convertible_to<T>;
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
};

template <typename Err> struct ExceptE {
  // DATA
  Err a0;

  // ACCESSORS
  ExceptE<Err> clone() const { return {a0}; }

  template <typename CraneU> operator ExceptE<CraneU>() const {
    return {[&]() -> CraneU {
      if constexpr (crane_convertible<CraneU, const Err &>) {
        return crane_convert<CraneU>(a0);
      } else {
        throw std::logic_error("unreachable: inactive constructor field at "
                               "this instantiation");
      }
    }()};
  }

  // CREATORS
  static ExceptE<Err> Throw_(Err a0) { return {std::move(a0)}; }
};

struct Err {
  // DATA
  std::string x;

  // ACCESSORS
  Err clone() const { return {x}; }

  // CREATORS
  static Err error(std::string x) { return {std::move(x)}; }
};

struct NatRef {
  // DATA
  uint64_t a;

  // ACCESSORS
  NatRef clone() const { return {a}; }

  // CREATORS
  static NatRef mknatref(uint64_t a) { return {a}; }

  uint64_t nat_ref_index() const {
    const auto &[a] = *this;
    return a;
  }
};

struct nat_ref_class {
  static crane::obj make_ref(uint64_t x) { return NatRef::mknatref(x); }

  static uint64_t ref_index(crane::obj _p_a0) {
    NatRef a0 = crane::any_cast<NatRef>(_p_a0);
    return a0.nat_ref_index();
  }
};

static_assert(RefClass<nat_ref_class, uint64_t>);

struct GlobalIndexedValueType {
  /// The value types as a global definition.
  template <typename x = void> using VD = crane::obj;

  /// n empty lists, the second then set to [x; y], read back.
  template <typename T1>
  static List<List<T1>> lists_notation(uint64_t n, const T1 &x, const T1 &y) {
    std::shared_ptr<crane::array_storage<List<T1>>> arr =
        std::make_shared<crane::array_storage<List<T1>>>(
            static_cast<std::size_t>(n), List<T1>::nil());
    std::span{*arr}[UINT64_C(1)] =
        List<T1>::cons(x, List<T1>::cons(y, List<T1>::nil()));
    return crane::st::elems<List<List<T1>>>(std::span{std::as_const(*arr)});
  }

  /// The same over the global definition.
  template <typename T1>
  static List<List<T1>> lists_definition(uint64_t n, const T1 &x, const T1 &y) {
    return lists_notation<T1>(n, x, y);
  }

  /// A reference at index 1 holds an X.
  template <typename T1> static T1 number_definition(T1 x) {
    std::shared_ptr<T1> r = std::make_shared<T1>(std::move(x));
    return *r;
  }

  /// At a concrete element type.
  static List<List<uint64_t>> lists_concrete(uint64_t n);
  static List<List<uint64_t>> via_notation(uint64_t n);
  static List<List<uint64_t>> via_definition(uint64_t n);
  static uint64_t number();
};
