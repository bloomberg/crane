#ifndef INCLUDED_LOOPIFY_COMBINATORICS
#define INCLUDED_LOOPIFY_COMBINATORICS

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  std::shared_ptr<List<t_A>> app(std::shared_ptr<List<t_A>> m) const {
    std::shared_ptr<List<t_A>> _head{};
    std::shared_ptr<List<t_A>> _last{};
    const List *_loop_self = this;
    bool _continue = true;
    while (_continue) {
      std::visit(
          Overloaded{
              [&](const typename List<t_A>::Nil) {
                if (_last) {
                  std::get<typename List<t_A>::Cons>(_last->v_mut()).d_a1 = m;
                } else {
                  _head = m;
                }
                _continue = false;
              },
              [&](const typename List<t_A>::Cons _args) {
                auto _cell = List<t_A>::cons(_args.d_a0, nullptr);
                if (_last) {
                  std::get<typename List<t_A>::Cons>(_last->v_mut()).d_a1 =
                      _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                _loop_self = _args.d_a1.get();
              }},
          _loop_self->v());
    }
    return _head;
  }
};

/// Consolidated combinatorial algorithms.
struct LoopifyCombinatorics {
  /// remove x l removes first occurrence of x from list.
  static std::shared_ptr<List<unsigned int>>
  remove(const unsigned int x, const std::shared_ptr<List<unsigned int>> &l);
  /// Helper: prepend x to each list in lsts.
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> map_cons(
      const unsigned int x,
      const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &lsts);
  /// perms_choices_fuel fuel choices orig generates permutations by iterating
  /// over choices.  Single self-recursive function that handles both the choice
  /// iteration and the recursive subproblem, enabling full loopification.
  /// The match on remaining is hoisted out of the let-binding so that all
  /// recursive calls appear at the top level of each branch.
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  perms_choices_fuel(const unsigned int fuel,
                     const std::shared_ptr<List<unsigned int>> &choices,
                     const std::shared_ptr<List<unsigned int>> &orig);
  /// permutations_fuel fuel l generates all permutations of a list.
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  permutations_fuel(const unsigned int fuel,
                    const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static unsigned int
  len_list(const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static unsigned int
  factorial_impl(const unsigned int n);
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  permutations(const std::shared_ptr<List<unsigned int>>
                   &l); /// subsequences l generates all subsequences (subsets
                        /// preserving order).
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  subsequences(const std::shared_ptr<List<unsigned int>> &l);
  /// Helper for cartesian product.
  static std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
  map_pairs(const unsigned int y, const std::shared_ptr<List<unsigned int>> &l);
  /// cartesian l1 l2 Cartesian product of two lists.
  static std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
  cartesian(const std::shared_ptr<List<unsigned int>> &l1,
            const std::shared_ptr<List<unsigned int>> &l2);
  /// power_set l generates the power set (all subsets).
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  power_set(const std::shared_ptr<List<unsigned int>> &l);
  /// insert_everywhere x l inserts x at every position in l.
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  insert_everywhere(const unsigned int x,
                    std::shared_ptr<List<unsigned int>> l);
  /// Helper: check if element is in list.
  __attribute__((pure)) static bool
  elem(const unsigned int x, const std::shared_ptr<List<unsigned int>> &l);
  /// Helper: list length.
  __attribute__((pure)) static unsigned int
  len_impl(const std::shared_ptr<List<unsigned int>> &l);
  /// dedup l removes all duplicates (keeps first occurrence).
  static std::shared_ptr<List<unsigned int>>
  dedup_fuel(const unsigned int fuel,
             const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<unsigned int>>
  dedup(const std::shared_ptr<List<unsigned int>> &l);
};

#endif // INCLUDED_LOOPIFY_COMBINATORICS
