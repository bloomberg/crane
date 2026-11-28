#pragma once

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
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

  uint64_t length() const {
    const List<A> *_self = this;

    // Explicit stack replaces the non-tail recursion of length: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const List<A> *_self;
    };

    struct _after_length_in_Cons {};

    using _frame = std::variant<_call, _after_length_in_Cons>;
    uint64_t _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{_self});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[_, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_after_length_in_Cons{});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_after_length_in_Cons>(_popped));
        _stack.pop_back();
        _result = (_result + 1);
      }
    }
    return _result;
  }
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

  uint64_t nat_ref_index() const;
};

struct nat_ref_class {
  static crane::obj make_ref(uint64_t x) { return NatRef::mknatref(x); }

  static uint64_t ref_index(crane::obj _p_a0) {
    NatRef a0 = crane::any_cast<NatRef>(_p_a0);
    return a0.nat_ref_index();
  }
};

static_assert(RefClass<nat_ref_class, uint64_t>);

struct GlobalArrays {
  /// A global array of nats, made at index 0.
  using nat_array = std::shared_ptr<crane::array_storage<uint64_t>>;
  /// Write i * i into each of the first k cells, last first.
  static void fill_squares(std::span<uint64_t> arr, uint64_t k);
  /// The squares below n, built in a fresh array.
  static List<uint64_t> squares(uint64_t n);
  /// The sum of the first k cells of arr, read one at a time.
  static uint64_t sum_cells(std::span<const uint64_t> arr, uint64_t k,
                            uint64_t acc);
  /// The sum of xs, through an array made from it.
  static uint64_t sum_list(const List<uint64_t> &xs);
  /// xs with its first and last elements exchanged in an array.
  static List<uint64_t> swap_ends(const List<uint64_t> &xs);
  /// A written cell reads back the new value, its neighbours the default.
  static std::pair<uint64_t, uint64_t> write_then_read();
  /// Arrays and references share the store: a reference made after an array
  /// reads back its own value.
  static uint64_t array_then_ref();
};

inline uint64_t NatRef::nat_ref_index() const {
  const auto &[a] = *this;
  return a;
}
