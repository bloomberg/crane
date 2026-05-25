#ifndef INCLUDED_LOOPIFY_COMBINATORICS
#define INCLUDED_LOOPIFY_COMBINATORICS

#include <any>
#include <memory>
#include <utility>
#include <variant>
#include <vector>

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

  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  List<A> app(List<A> m) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return m;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return List<A>::cons(a0, a1->app(std::move(m)));
    }
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
  static List<List<uint64_t>> insert_everywhere(uint64_t x, List<uint64_t> l);
  /// Helper: check if element is in list.
  static bool elem(uint64_t x, const List<uint64_t> &l);
  /// Helper: list length.
  static uint64_t len_impl(const List<uint64_t> &l);
  /// dedup l removes all duplicates (keeps first occurrence).
  static List<uint64_t> dedup_fuel(uint64_t fuel, const List<uint64_t> &l);
  static List<uint64_t> dedup(const List<uint64_t> &l);
};

#endif // INCLUDED_LOOPIFY_COMBINATORICS
