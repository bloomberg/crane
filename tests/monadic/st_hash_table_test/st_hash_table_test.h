#pragma once

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "small_vector.h"
#include <algorithm>
#include <atomic>
#include <concepts>
#include <crane_itree.h>
#include <crane_st.h>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <optional>
#include <span>
#include <stdexcept>
#include <string>
#include <string_view>
#include <type_traits>
#include <utility>
#include <variant>

struct hashable_nat;
template <typename A> struct List;
template <typename Err> struct ExceptE;
struct Err;
enum class Refs;
template <typename K, typename A> struct state;
template <typename K, typename A> struct t;
template <typename k = void, typename a = void> using store = crane::obj;
template <typename I, typename A>
concept Hashable = requires {
  { I::hash(std::declval<A>()) } -> std::convertible_to<uint64_t>;
  { I::eqb(std::declval<A>(), std::declval<A>()) } -> std::convertible_to<bool>;
};

struct ListDef {
  static List<uint64_t> seq(uint64_t start, uint64_t len);
};

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

  template <typename T1> List<T1> concat() const {
    const List<A> *_self = this;

    // Explicit stack replaces the non-tail recursion of concat: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const List<A> *_self;
    };

    struct _after_concat_in_Cons {
      List<T1> a0;
    };

    using _frame = std::variant<_call, _after_concat_in_Cons>;
    List<T1> _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{_self});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<List<T1>>::Nil>(_sv.v())) {
          _result = List<T1>::nil();
        } else {
          const auto &[a0, a1] =
              std::get<typename List<List<T1>>::Cons>(_sv.v());
          _stack.emplace_back(_after_concat_in_Cons{a0});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_after_concat_in_Cons>(_popped));
        _stack.pop_back();
        List<T1> a0 = std::move(_f.a0);
        _result = a0.app(std::move(_result));
      }
    }
    return _result;
  }

  List<A> app(List<A> m) const {
    // Builds the result front to back: _write points at the empty tail the next
    // cell fills.
    std::optional<List<A>> _root{};
    std::shared_ptr<List<A>> *_write = nullptr;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = std::move(m);
        (_write ? *(*_write = std::make_shared<List<A>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell = typename List<A>::Cons(a0, nullptr);
        List<A> &_node =
            (_write ? *(*_write = std::make_shared<List<A>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<A>::Cons>(_node.v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
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

template <typename k, typename a> using bucket = List<std::pair<k, a>>;

struct HashTableDefs {
  template <typename _tcI0, typename T1>
    requires Hashable<_tcI0, T1>
  static uint64_t index(const T1 &k, uint64_t n);
  template <typename _tcI0, typename T1, typename T2>
    requires Hashable<_tcI0, T1>
  static std::optional<T2> bucket_find(const T1 &k,
                                       const List<std::pair<T1, T2>> &b);
  template <typename _tcI0, typename T1, typename T2>
    requires Hashable<_tcI0, T1>
  static bucket<T1, T2> bucket_remove(const T1 &k,
                                      const List<std::pair<T1, T2>> &b);
  template <typename _tcI0, typename T1, typename T2>
    requires Hashable<_tcI0, T1>
  static bucket<T1, T2> bucket_put(const T1 &k, const std::optional<T2> &o,
                                   const List<std::pair<T1, T2>> &b);
  template <typename T1> static bool present(const std::optional<T1> &o);
  static constexpr uint64_t default_capacity = UINT64_C(8);
};

struct hashable_nat {
  constexpr static uint64_t hash(uint64_t n) { return n; }

  constexpr static bool eqb(uint64_t a0, uint64_t a1) { return a0 == a1; }
};

static_assert(Hashable<hashable_nat, uint64_t>);
enum class Refs { BUILD_REFS };

struct ST {
  template <typename T2, typename T3, typename F2>
  static T3 for_each_with(const List<T2> &xs, const T3 &v, F2 &&f);
};

template <typename K, typename A> struct state {
  std::shared_ptr<crane::array_storage<bucket<K, A>>> buckets;
  uint64_t capacity;
  uint64_t count;

  // ACCESSORS
  template <typename CraneU0, typename CraneU1>
  operator state<CraneU0, CraneU1>() const {
    return {std::shared_ptr<crane::array_storage<bucket<CraneU0, CraneU1>>>(
        buckets),
            capacity, count};
  }
};

template <typename K, typename A> struct t {
  std::shared_ptr<state<K, A>> cell;

  // ACCESSORS
  template <typename CraneU0, typename CraneU1>
  operator t<CraneU0, CraneU1>() const {
    return {std::shared_ptr<state<CraneU0, CraneU1>>(cell)};
  }
};

struct STHashTable {
  template <typename T1, typename T2, typename T3 = void>
  static t<T1, T2> new_sized(uint64_t n);
  template <typename T1, typename T2, typename T3 = void>
  static t<T1, T2> new0();
  template <typename T1, typename T2, typename T3 = void>
  static uint64_t size(const t<T1, T2> &tbl);
  template <typename _tcI0, typename T1, typename T2, typename T3 = void>
    requires Hashable<_tcI0, T1>
  static std::optional<T2> lookup(const t<T1, T2> &tbl, const T1 &k);
  template <typename _tcI0, typename T1, typename T2, typename T3 = void>
    requires Hashable<_tcI0, T1>
  static void place(std::span<List<std::pair<T1, T2>>> arr, uint64_t cap,
                    const T1 &k, const T2 &v);
  template <typename _tcI0, typename T1, typename T2, typename T3 = void>
    requires Hashable<_tcI0, T1>
  static void grow(const t<T1, T2> &tbl, const state<T1, T2> &s);
  template <typename _tcI0, typename T1, typename T2, typename T3 = void>
    requires Hashable<_tcI0, T1>
  static void set_count(const t<T1, T2> &tbl, const state<T1, T2> &s,
                        uint64_t n);
  template <typename _tcI0, typename T1, typename T2, typename T3 = void,
            typename F2>
    requires Hashable<_tcI0, T1> &&
             std::is_invocable_r_v<std::optional<T2>, F2 &, std::optional<T2> &>
  static void alter(const t<T1, T2> &tbl, const T1 &k, F2 &&f);
  template <typename _tcI0, typename T1, typename T2, typename T3 = void>
    requires Hashable<_tcI0, T1>
  static void insert(const t<T1, T2> &tbl, const T1 &k, const T2 &v);
  template <typename _tcI0, typename T1, typename T2, typename T3 = void>
    requires Hashable<_tcI0, T1>
  static void delete0(const t<T1, T2> &tbl, const T1 &k);
  template <typename T1, typename T2, typename T3 = void, typename T5>
  static T5 fold(std::type_identity_t<crane::fn<T5(T5, T1, T2)>> f, const T5 &z,
                 const t<T1, T2> &tbl);
  template <typename T1, typename T2, typename T3 = void>
  static void iter(const std::type_identity_t<crane::fn<void(T1, T2)>> &f,
                   const t<T1, T2> &tbl);
  template <typename T1, typename T2, typename T3 = void>
  static List<std::pair<T1, T2>> to_list(const t<T1, T2> &tbl);
  template <typename _tcI0, typename T1, typename T2, typename T3 = void>
    requires Hashable<_tcI0, T1>
  static t<T1, T2> of_list(const List<std::pair<T1, T2>> &kvs);
};

/// Binds k to k * k for every k of ks.
void insert_squares(t<uint64_t, uint64_t> tbl, const List<uint64_t> &ks);
/// growth, run in C++.
std::pair<std::pair<std::pair<uint64_t, std::optional<uint64_t>>,
                    std::optional<uint64_t>>,
          List<std::pair<uint64_t, uint64_t>>> growth(uint64_t n);
/// delete_reinsert, run in C++.
std::pair<
    std::pair<std::pair<std::pair<std::optional<uint64_t>, uint64_t>, uint64_t>,
              std::optional<uint64_t>>,
    uint64_t> delete_reinsert();
/// Counts one more occurrence of k.
void bump(const t<uint64_t, uint64_t> &tbl, uint64_t k);
/// counts, run in C++.
std::pair<uint64_t, List<std::pair<uint64_t, uint64_t>>>
counts(const List<uint64_t> &xs);
/// fold_iter, run in C++.
std::pair<std::pair<uint64_t, uint64_t>, List<std::pair<uint64_t, uint64_t>>>
fold_iter(const List<std::pair<uint64_t, uint64_t>> &kvs);

struct STHashTableTest {
  /// growth, run in C++.
  static std::pair<std::pair<std::pair<uint64_t, std::optional<uint64_t>>,
                             std::optional<uint64_t>>,
                   List<std::pair<uint64_t, uint64_t>>> growth(uint64_t n);
  /// delete_reinsert, run in C++.
  static inline const std::pair<std::pair<
      std::pair<std::pair<std::optional<uint64_t>, uint64_t>, uint64_t>,
      std::optional<uint64_t>>,
                                uint64_t> delete_reinsert = ::delete_reinsert();
  /// counts, run in C++.
  static std::pair<uint64_t, List<std::pair<uint64_t, uint64_t>>>
  counts(const List<uint64_t> &xs);
  /// fold_iter, run in C++.
  static std::pair<std::pair<uint64_t, uint64_t>,
                   List<std::pair<uint64_t, uint64_t>>>
  fold_iter(const List<std::pair<uint64_t, uint64_t>> &kvs);
};

template <typename _tcI0, typename T1>
  requires Hashable<_tcI0, T1>
uint64_t HashTableDefs::index(const T1 &k, uint64_t n) {
  auto _once1 = _tcI0::hash(k);
  return (n ? _once1 % n : _once1);
}

template <typename _tcI0, typename T1, typename T2>
  requires Hashable<_tcI0, T1>
std::optional<T2> HashTableDefs::bucket_find(const T1 &k,
                                             const List<std::pair<T1, T2>> &b) {
  if (std::holds_alternative<typename List<std::pair<T1, T2>>::Nil>(b.v())) {
    return std::optional<T2>();
  } else {
    const auto &[a0, a1] =
        std::get<typename List<std::pair<T1, T2>>::Cons>(b.v());
    const auto &[k_, v] = a0;
    if (_tcI0::eqb(k, k_)) {
      return std::make_optional<T2>(v);
    } else {
      return HashTableDefs::template bucket_find<_tcI0, T1, T2>(k, *a1);
    }
  }
}

template <typename _tcI0, typename T1, typename T2>
  requires Hashable<_tcI0, T1>
bucket<T1, T2> HashTableDefs::bucket_remove(const T1 &k,
                                            const List<std::pair<T1, T2>> &b) {
  if (std::holds_alternative<typename List<std::pair<T1, T2>>::Nil>(b.v())) {
    return List<std::pair<T1, T2>>::nil();
  } else {
    const auto &[a0, a1] =
        std::get<typename List<std::pair<T1, T2>>::Cons>(b.v());
    const auto &[k_, v] = a0;
    if (_tcI0::eqb(k, k_)) {
      return *a1;
    } else {
      return List<std::pair<T1, T2>>::cons(
          std::make_pair(k_, v),
          HashTableDefs::template bucket_remove<_tcI0, T1, T2>(k, *a1));
    }
  }
}

template <typename _tcI0, typename T1, typename T2>
  requires Hashable<_tcI0, T1>
bucket<T1, T2>
HashTableDefs::bucket_put(const T1 &k, const std::optional<T2> &o,
                          const List<std::pair<T1, T2>> &b) {
  if (o.has_value()) {
    const T2 &v = *o;
    return List<std::pair<T1, T2>>::cons(
        std::make_pair(k, v),
        HashTableDefs::template bucket_remove<_tcI0, T1, T2>(k, b));
  } else {
    return HashTableDefs::template bucket_remove<_tcI0, T1, T2>(k, b);
  }
}

template <typename T1> bool HashTableDefs::present(const std::optional<T1> &o) {
  if (o.has_value()) {
    const T1 &_x = *o;
    return true;
  } else {
    return false;
  }
}

template <typename T2, typename T3, typename F2>
T3 ST::for_each_with(const List<T2> &xs, const T3 &v, F2 &&f) {
  if (std::holds_alternative<typename List<T2>::Nil>(xs.v())) {
    return v;
  } else {
    const auto &[a0, a1] = std::get<typename List<T2>::Cons>(xs.v());
    return ST::template for_each_with<T2, T3>(*a1, f(v, a0), f);
  }
}

template <typename T1, typename T2, typename T3>
t<T1, T2> STHashTable::new_sized(uint64_t n) {
  uint64_t cap = std::max(n, UINT64_C(1));
  std::shared_ptr<crane::array_storage<List<std::pair<T1, T2>>>> arr =
      std::make_shared<crane::array_storage<List<std::pair<T1, T2>>>>(
          static_cast<std::size_t>(cap), List<std::pair<T1, T2>>::nil());
  std::shared_ptr<state<T1, T2>> r = std::make_shared<state<T1, T2>>(
      state<T1, T2>{std::move(arr), cap, UINT64_C(0)});
  return t<T1, T2>{std::move(r)};
}

template <typename T1, typename T2, typename T3> t<T1, T2> STHashTable::new0() {
  return STHashTable::template new_sized<T1, T2, crane::obj>(
      HashTableDefs::default_capacity);
}

template <typename T1, typename T2, typename T3>
uint64_t STHashTable::size(const t<T1, T2> &tbl) {
  return (*tbl.cell.get()).count;
}

template <typename _tcI0, typename T1, typename T2, typename T3>
  requires Hashable<_tcI0, T1>
std::optional<T2> STHashTable::lookup(const t<T1, T2> &tbl, const T1 &k) {
  state<T1, T2> s = *tbl.cell.get();
  List<std::pair<T1, T2>> b = std::span{std::as_const(*s.buckets)}[
      HashTableDefs::template index<_tcI0, T1>(k, s.capacity)];
  return HashTableDefs::template bucket_find<_tcI0, T1, T2>(k, std::move(b));
}

template <typename _tcI0, typename T1, typename T2, typename T3>
  requires Hashable<_tcI0, T1>
void STHashTable::place(std::span<List<std::pair<T1, T2>>> arr, uint64_t cap,
                        const T1 &k, const T2 &v) {
  uint64_t i = HashTableDefs::template index<_tcI0, T1>(k, cap);
  List<std::pair<T1, T2>> b = arr[i];
  arr[i] = List<std::pair<T1, T2>>::cons(std::make_pair(k, v), std::move(b));
}

template <typename _tcI0, typename T1, typename T2, typename T3>
  requires Hashable<_tcI0, T1>
void STHashTable::grow(const t<T1, T2> &tbl, const state<T1, T2> &s) {
  uint64_t cap = UINT64_C(2) * s.capacity;
  std::shared_ptr<crane::array_storage<List<std::pair<T1, T2>>>> arr =
      std::make_shared<crane::array_storage<List<std::pair<T1, T2>>>>(
          static_cast<std::size_t>(cap), List<std::pair<T1, T2>>::nil());
  List<List<std::pair<T1, T2>>> bs = crane::st::elems<List<bucket<T1, T2>>>(
      std::span{std::as_const(*s.buckets)});
  ST::template for_each_with<bucket<T1, T2>, std::monostate>(
      std::move(bs), std::monostate{},
      [=](std::monostate, const List<std::pair<T1, T2>> &b) {
        return ST::template for_each_with<std::pair<T1, T2>, std::monostate>(
            b, std::monostate{},
            [=, arr = arr](std::monostate, const std::pair<T1, T2> &kv) {
              STHashTable::template place<_tcI0, T1, T2, crane::obj>(
                  std::span{*arr}, cap, kv.first, kv.second);
              return std::monostate{};
            });
      });
  auto _once1 = tbl.cell;
  auto _once2 = state<T1, T2>{std::move(arr), cap, s.count};
  *_once1.get() = std::move(_once2);
}

template <typename _tcI0, typename T1, typename T2, typename T3>
  requires Hashable<_tcI0, T1>
void STHashTable::set_count(const t<T1, T2> &tbl, const state<T1, T2> &s,
                            uint64_t n) {
  state<T1, T2> s_ = state<T1, T2>{s.buckets, s.capacity, n};
  if (s.capacity < n) {
    STHashTable::template grow<_tcI0, T1, T2, crane::obj>(tbl, std::move(s_));
  } else {
    auto _once1 = tbl.cell;
    auto _once2 = std::move(s_);
    *_once1.get() = std::move(_once2);
  }
}

template <typename _tcI0, typename T1, typename T2, typename T3, typename F2>
  requires Hashable<_tcI0, T1> &&
           std::is_invocable_r_v<std::optional<T2>, F2 &, std::optional<T2> &>
void STHashTable::alter(const t<T1, T2> &tbl, const T1 &k, F2 &&f) {
  state<T1, T2> s = *tbl.cell.get();
  uint64_t i = HashTableDefs::template index<_tcI0, T1>(k, s.capacity);
  List<std::pair<T1, T2>> b = std::span{std::as_const(*s.buckets)}[i];
  std::optional<T2> old =
      HashTableDefs::template bucket_find<_tcI0, T1, T2>(k, b);
  std::optional<T2> upd = f(old);
  auto _once1 = s.buckets;
  auto _once2 =
      HashTableDefs::template bucket_put<_tcI0, T1, T2>(k, upd, std::move(b));
  std::span{*_once1}[i] = std::move(_once2);
  if (HashTableDefs::template present<T2>(std::move(old))) {
    if (HashTableDefs::template present<T2>(std::move(upd))) {
      return;
    } else {
      STHashTable::template set_count<_tcI0, T1, T2, crane::obj>(
          tbl, s, (s.count ? s.count - 1 : s.count));
    }
  } else if (HashTableDefs::template present<T2>(std::move(upd))) {
    STHashTable::template set_count<_tcI0, T1, T2, crane::obj>(tbl, s,
                                                               (s.count + 1));
  }
}

template <typename _tcI0, typename T1, typename T2, typename T3>
  requires Hashable<_tcI0, T1>
void STHashTable::insert(const t<T1, T2> &tbl, const T1 &k, const T2 &v) {
  STHashTable::template alter<_tcI0, T1, T2, crane::obj>(
      tbl, k,
      [=, v = v](std::optional<T2>) { return std::make_optional<T2>(v); });
}

template <typename _tcI0, typename T1, typename T2, typename T3>
  requires Hashable<_tcI0, T1>
void STHashTable::delete0(const t<T1, T2> &tbl, const T1 &k) {
  STHashTable::template alter<_tcI0, T1, T2, crane::obj>(
      tbl, k, [](std::optional<T2>) { return std::optional<T2>(); });
}

template <typename T1, typename T2, typename T3, typename T5>
T5 STHashTable::fold(std::type_identity_t<crane::fn<T5(T5, T1, T2)>> f,
                     const T5 &z, const t<T1, T2> &tbl) {
  state<T1, T2> s = *tbl.cell.get();
  List<List<std::pair<T1, T2>>> bs = crane::st::elems<List<bucket<T1, T2>>>(
      std::span{std::as_const(*s.buckets)});
  return ST::template for_each_with<bucket<T1, T2>, T5>(
      std::move(bs), z,
      [=, f = std::move(f)](const T5 &acc, const List<std::pair<T1, T2>> &b) {
        return ST::template for_each_with<std::pair<T1, T2>, T5>(
            b, acc, [=, f = f](const T5 &acc_,
                               const std::pair<T1,
                                               T2> &kv) {
                      return f(acc_, kv.first, kv.second);
                    });
      });
}

template <typename T1, typename T2, typename T3>
void STHashTable::iter(const std::type_identity_t<crane::fn<void(T1, T2)>> &f,
                       const t<T1, T2> &tbl) {
  {
    STHashTable::template fold<T1, T2, crane::obj, std::monostate>(
        [=, f = f](std::monostate, const T1 &eta0_, const T2 &eta1_) {
          f(eta0_, eta1_);
          return std::monostate{};
        },
        std::monostate{},
        tbl);
  }
}

template <typename T1, typename T2, typename T3>
List<std::pair<T1, T2>> STHashTable::to_list(const t<T1, T2> &tbl) {
  state<T1, T2> s = *tbl.cell.get();
  List<List<std::pair<T1, T2>>> bs = crane::st::elems<List<bucket<T1, T2>>>(
      std::span{std::as_const(*s.buckets)});
  return bs.template concat<std::pair<T1, T2>>();
}

template <typename _tcI0, typename T1, typename T2, typename T3>
  requires Hashable<_tcI0, T1>
t<T1, T2> STHashTable::of_list(const List<std::pair<T1, T2>> &kvs) {
  t<T1, T2> tbl = STHashTable::template new0<T1, T2, crane::obj>();
  ST::template for_each_with<std::pair<T1, T2>, std::monostate>(
      kvs, std::monostate{}, [=](std::monostate, const std::pair<T1, T2> &kv) {
        STHashTable::template insert<_tcI0, T1, T2, crane::obj>(tbl, kv.first,
                                                                kv.second);
        return std::monostate{};
      });
  return tbl;
}
