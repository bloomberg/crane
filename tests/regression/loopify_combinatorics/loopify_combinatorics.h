#ifndef INCLUDED_LOOPIFY_COMBINATORICS
#define INCLUDED_LOOPIFY_COMBINATORICS

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
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

  List<A> app(List<A> m) const {
    std::optional<List<A>> _root{};
    std::shared_ptr<List<A>> *_write = nullptr;
    const List<A> *_loop_self = this;
    List<A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = std::move(_loop_m);
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

/// Consolidated combinatorial algorithms.
struct LoopifyCombinatorics {
  /// remove x l removes first occurrence of x from list.
  static List<uint64_t> remove(uint64_t x, const List<uint64_t> &l);
  /// Helper: prepend x to each list in lsts.
  static List<List<uint64_t>> map_cons(uint64_t x,
                                       const List<List<uint64_t>> &lsts);
  /// perms_choices_fuel fuel choices orig generates permutations by iterating
  /// over choices.  Single self-recursive function that handles both the choice
  /// iteration and the recursive subproblem, enabling full loopification.
  /// The match on remaining is hoisted out of the let-binding so that all
  /// recursive calls appear at the top level of each branch.
  static List<List<uint64_t>> perms_choices_fuel(uint64_t fuel,
                                                 const List<uint64_t> &choices,
                                                 const List<uint64_t> &orig);
  /// permutations_fuel fuel l generates all permutations of a list.
  static List<List<uint64_t>> permutations_fuel(uint64_t fuel,
                                                const List<uint64_t> &l);
  static uint64_t len_list(const List<uint64_t> &l);
  static uint64_t factorial_impl(uint64_t n);
  static List<List<uint64_t>> permutations(const List<uint64_t> &l);
  /// subsequences l generates all subsequences (subsets preserving order).
  static List<List<uint64_t>> subsequences(const List<uint64_t> &l);
  /// Helper for cartesian product.
  static List<std::pair<uint64_t, uint64_t>> map_pairs(uint64_t y,
                                                       const List<uint64_t> &l);
  /// cartesian l1 l2 Cartesian product of two lists.
  static List<std::pair<uint64_t, uint64_t>>
  cartesian(const List<uint64_t> &l1, const List<uint64_t> &l2);
  /// power_set l generates the power set (all subsets).
  static List<List<uint64_t>> power_set(const List<uint64_t> &l);
  /// insert_everywhere x l inserts x at every position in l.
  static List<List<uint64_t>> insert_everywhere(uint64_t x,
                                                const List<uint64_t> &l);
  /// Helper: check if element is in list.
  static bool elem(uint64_t x, const List<uint64_t> &l);
  /// Helper: list length.
  static uint64_t len_impl(const List<uint64_t> &l);
  /// dedup l removes all duplicates (keeps first occurrence).
  static List<uint64_t> dedup_fuel(uint64_t fuel, const List<uint64_t> &l);
  static List<uint64_t> dedup(const List<uint64_t> &l);
};

#endif // INCLUDED_LOOPIFY_COMBINATORICS
