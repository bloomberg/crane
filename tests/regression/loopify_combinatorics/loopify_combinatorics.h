#ifndef INCLUDED_LOOPIFY_COMBINATORICS
#define INCLUDED_LOOPIFY_COMBINATORICS

#include <memory>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a0;
    std::unique_ptr<List<A>> a1;
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

  List(const List<A> &_other) : v_(std::move(_other.clone().v_)) {}

  List(List<A> &&_other) : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  List<A> clone() const {
    List<A> _out{};

    struct _CloneFrame {
      const List<A> *_src;
      List<A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<A> *_src = _frame._src;
      List<A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->v_ =
            Cons{_alt.a0, _alt.a1 ? std::make_unique<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.a1) {
          _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a0, a1] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a0), a1 ? std::make_unique<List<A>>(*a1) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a0, List<A> a1) {
    return List(Cons{std::move(a0), std::make_unique<List<A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
        if (_alt.a1) {
          _stack.push_back(std::move(_alt.a1));
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

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  List<A> app(List<A> m) const {
    std::unique_ptr<List<A>> _head{};
    std::unique_ptr<List<A>> *_write = &_head;
    const List *_loop_self = this;
    List<A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        *_write = std::make_unique<List<A>>(std::move(_loop_m));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell =
            std::make_unique<List<A>>(typename List<A>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<A>::Cons>((*_write)->v_mut()).a1;
        _loop_self = a1.get();
        continue;
      }
    }
    return std::move(*_head);
  }
};

/// Consolidated combinatorial algorithms.
struct LoopifyCombinatorics {
  /// remove x l removes first occurrence of x from list.
  static List<unsigned int> remove(unsigned int x, const List<unsigned int> &l);
  /// Helper: prepend x to each list in lsts.
  static List<List<unsigned int>>
  map_cons(unsigned int x, const List<List<unsigned int>> &lsts);
  /// perms_choices_fuel fuel choices orig generates permutations by iterating
  /// over choices.  Single self-recursive function that handles both the choice
  /// iteration and the recursive subproblem, enabling full loopification.
  /// The match on remaining is hoisted out of the let-binding so that all
  /// recursive calls appear at the top level of each branch.
  static List<List<unsigned int>>
  perms_choices_fuel(unsigned int fuel, const List<unsigned int> &choices,
                     const List<unsigned int> &orig);
  /// permutations_fuel fuel l generates all permutations of a list.
  static List<List<unsigned int>>
  permutations_fuel(unsigned int fuel, const List<unsigned int> &l);
  static unsigned int len_list(const List<unsigned int> &l);
  static unsigned int factorial_impl(unsigned int n);
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
  static bool elem(unsigned int x, const List<unsigned int> &l);
  /// Helper: list length.
  static unsigned int len_impl(const List<unsigned int> &l);
  /// dedup l removes all duplicates (keeps first occurrence).
  static List<unsigned int> dedup_fuel(unsigned int fuel,
                                       const List<unsigned int> &l);
  static List<unsigned int> dedup(const List<unsigned int> &l);
};

#endif // INCLUDED_LOOPIFY_COMBINATORICS
