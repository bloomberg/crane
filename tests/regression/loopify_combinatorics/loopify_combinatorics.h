#ifndef INCLUDED_LOOPIFY_COMBINATORICS
#define INCLUDED_LOOPIFY_COMBINATORICS

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  List<t_A> clone() const {
    List<t_A> _out{};

    struct _CloneFrame {
      const List<t_A> *_src;
      List<t_A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<t_A> *_src = _frame._src;
      List<t_A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->d_v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->d_v_ = Cons{_alt.d_a0,
                          _alt.d_a1 ? std::make_unique<List<t_A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->d_v_);
        if (_alt.d_a1) {
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  static List<t_A> nil() { return List(Nil{}); }

  static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons{std::move(a0), std::make_unique<List<t_A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<t_A>>> _stack{};
    auto _drain = [&](List<t_A> &_node) {
      if (std::holds_alternative<Cons>(_node.d_v_)) {
        auto &_alt = std::get<Cons>(_node.d_v_);
        if (_alt.d_a1) {
          _stack.push_back(std::move(_alt.d_a1));
        }
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node) {
        _drain(*_node);
      }
    }
  }

  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }

  List<t_A> app(List<t_A> m) const {
    std::unique_ptr<List<t_A>> _head{};
    std::unique_ptr<List<t_A>> *_write = &_head;
    const List *_loop_self = this;
    List<t_A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *(_loop_self);
      if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
        *(_write) = std::make_unique<List<t_A>>(std::move(_loop_m));
        break;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
        auto _cell = std::make_unique<List<t_A>>(
            typename List<t_A>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write = &std::get<typename List<t_A>::Cons>((*_write)->v_mut()).d_a1;
        const List *_next_self = d_a1.get();
        List<t_A> _next_m = std::move(_loop_m);
        _loop_self = _next_self;
        _loop_m = std::move(_next_m);
        continue;
      }
    }
    return std::move(*(_head));
  }
};

/// Consolidated combinatorial algorithms.
struct LoopifyCombinatorics {
  /// remove x l removes first occurrence of x from list.
  static List<unsigned int> remove(const unsigned int &x,
                                   const List<unsigned int> &l);
  /// Helper: prepend x to each list in lsts.
  static List<List<unsigned int>>
  map_cons(unsigned int x, const List<List<unsigned int>> &lsts);
  /// perms_choices_fuel fuel choices orig generates permutations by iterating
  /// over choices.  Single self-recursive function that handles both the choice
  /// iteration and the recursive subproblem, enabling full loopification.
  /// The match on remaining is hoisted out of the let-binding so that all
  /// recursive calls appear at the top level of each branch.
  static List<List<unsigned int>>
  perms_choices_fuel(const unsigned int &fuel,
                     const List<unsigned int> &choices,
                     const List<unsigned int> &orig);
  /// permutations_fuel fuel l generates all permutations of a list.
  static List<List<unsigned int>>
  permutations_fuel(const unsigned int &fuel, const List<unsigned int> &l);
  static unsigned int len_list(const List<unsigned int> &l);
  static unsigned int factorial_impl(const unsigned int &n);
  static List<List<unsigned int>> permutations(const List<unsigned int> &l);
  /// subsequences l generates all subsequences (subsets preserving order).
  static List<List<unsigned int>> subsequences(const List<unsigned int> &l);
  /// Helper for cartesian product.
  static List<std::pair<unsigned int, unsigned int>>
  map_pairs(unsigned int y, const List<unsigned int> &l);
  /// cartesian l1 l2 Cartesian product of two lists.
  static List<std::pair<unsigned int, unsigned int>>
  cartesian(const List<unsigned int> &l1, const List<unsigned int> &l2);
  /// power_set l generates the power set (all subsets).
  static List<List<unsigned int>> power_set(const List<unsigned int> &l);
  /// insert_everywhere x l inserts x at every position in l.
  static List<List<unsigned int>> insert_everywhere(unsigned int x,
                                                    List<unsigned int> l);
  /// Helper: check if element is in list.
  static bool elem(const unsigned int &x, const List<unsigned int> &l);
  /// Helper: list length.
  static unsigned int len_impl(const List<unsigned int> &l);
  /// dedup l removes all duplicates (keeps first occurrence).
  static List<unsigned int> dedup_fuel(const unsigned int &fuel,
                                       const List<unsigned int> &l);
  static List<unsigned int> dedup(const List<unsigned int> &l);
};

#endif // INCLUDED_LOOPIFY_COMBINATORICS
