#ifndef INCLUDED_LOOPIFY_SEQUENCES
#define INCLUDED_LOOPIFY_SEQUENCES

#include <memory>
#include <type_traits>
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

  List(List<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) noexcept {
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

  unsigned int length() const {
    const List *_self = this;

    /// _Enter: captures varying parameters for each recursive call.
    struct _Enter {
      const List *_self;
    };

    /// _Resume_Cons: resumes after recursive call with _result.
    struct _Resume_Cons {};

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{_self});
    /// Loopified length: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = 0u;
        } else {
          const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_Resume_Cons{});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = (_result + 1);
      }
    }
    return _result;
  }

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

struct LoopifySequences {
  /// alternate_sum sign acc l alternating sum with sign flip.
  static unsigned int alternate_sum(unsigned int sign, unsigned int acc,
                                    const List<unsigned int> &l);

  /// intercalate sep lists inserts sep between lists and flattens.
  template <typename T1>
  static List<T1> intercalate(
      const List<T1> &sep,
      const List<List<T1>> &lists) { /// _Enter: captures varying parameters for
                                     /// each recursive call.

    struct _Enter {
      const List<List<T1>> *lists;
    };

    /// _Resume_Cons: saves [a0, sep], resumes after recursive call with
    /// _result.
    struct _Resume_Cons {
      List<T1> a0;
      List<T1> sep;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    List<T1> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&lists});
    /// Loopified intercalate: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<List<T1>> &lists = *_f.lists;
        if (std::holds_alternative<typename List<List<T1>>::Nil>(lists.v())) {
          _result = List<T1>::nil();
        } else {
          const auto &[a0, a1] =
              std::get<typename List<List<T1>>::Cons>(lists.v());
          auto &&_sv = *a1;
          if (std::holds_alternative<typename List<List<T1>>::Nil>(_sv.v())) {
            _result = std::move(a0);
          } else {
            _stack.emplace_back(_Resume_Cons{a0, sep});
            _stack.emplace_back(_Enter{a1.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = _f.a0.app(_f.sep.app(_result));
      }
    }
    return _result;
  }

  /// join_with sep l joins list elements with separator.
  template <typename T1> static List<T1> join_with(T1 sep, const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return List<T1>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      auto go_impl = [&](auto &_self_go, const List<T1> &rest) -> List<T1> {
        if (std::holds_alternative<typename List<T1>::Nil>(rest.v())) {
          return List<T1>::nil();
        } else {
          const auto &[a00, a10] = std::get<typename List<T1>::Cons>(rest.v());
          return List<T1>::cons(sep,
                                List<T1>::cons(a00, _self_go(_self_go, *a10)));
        }
      };
      auto go = [&](const List<T1> &rest) -> List<T1> {
        return go_impl(go_impl, rest);
      };
      return List<T1>::cons(a0, go(*a1));
    }
  } /// transpose l transposes a list of lists.

  template <typename T1>
  static List<List<T1>> transpose_fuel(unsigned int fuel,
                                       const List<List<T1>> &ll) {
    std::unique_ptr<List<List<T1>>> _head{};
    std::unique_ptr<List<List<T1>>> *_write = &_head;
    List<List<T1>> _loop_ll = ll;
    unsigned int _loop_fuel = std::move(fuel);
    while (true) {
      if (_loop_fuel <= 0) {
        *_write = std::make_unique<List<List<T1>>>(List<List<T1>>::nil());
        break;
      } else {
        unsigned int f = _loop_fuel - 1;
        auto all_nil_impl = [](auto &_self_all_nil,
                               const List<List<T1>> &l) -> bool {
          if (std::holds_alternative<typename List<List<T1>>::Nil>(l.v())) {
            return true;
          } else {
            const auto &[a0, a1] =
                std::get<typename List<List<T1>>::Cons>(l.v());
            if (std::holds_alternative<typename List<T1>::Nil>(a0.v())) {
              return _self_all_nil(_self_all_nil, *a1);
            } else {
              return false;
            }
          }
        };
        auto all_nil = [&](const List<List<T1>> &l) -> bool {
          return all_nil_impl(all_nil_impl, l);
        };
        if (all_nil(_loop_ll)) {
          *_write = std::make_unique<List<List<T1>>>(List<List<T1>>::nil());
          break;
        } else {
          auto heads_impl = [](auto &_self_heads,
                               const List<List<T1>> &l) -> List<T1> {
            if (std::holds_alternative<typename List<List<T1>>::Nil>(l.v())) {
              return List<T1>::nil();
            } else {
              const auto &[a00, a10] =
                  std::get<typename List<List<T1>>::Cons>(l.v());
              if (std::holds_alternative<typename List<T1>::Nil>(a00.v())) {
                return _self_heads(_self_heads, *a10);
              } else {
                const auto &[a01, a11] =
                    std::get<typename List<T1>::Cons>(a00.v());
                return List<T1>::cons(a01, _self_heads(_self_heads, *a10));
              }
            }
          };
          auto heads = [&](const List<List<T1>> &l) -> List<T1> {
            return heads_impl(heads_impl, l);
          };
          auto tails_impl = [](auto &_self_tails,
                               const List<List<T1>> &l) -> List<List<T1>> {
            if (std::holds_alternative<typename List<List<T1>>::Nil>(l.v())) {
              return List<List<T1>>::nil();
            } else {
              const auto &[a01, a11] =
                  std::get<typename List<List<T1>>::Cons>(l.v());
              if (std::holds_alternative<typename List<T1>::Nil>(a01.v())) {
                return _self_tails(_self_tails, *a11);
              } else {
                const auto &[a02, a12] =
                    std::get<typename List<T1>::Cons>(a01.v());
                return List<List<T1>>::cons(*a12,
                                            _self_tails(_self_tails, *a11));
              }
            }
          };
          auto tails = [&](const List<List<T1>> &l) -> List<List<T1>> {
            return tails_impl(tails_impl, l);
          };
          auto _cell = std::make_unique<List<List<T1>>>(
              typename List<List<T1>>::Cons(heads(_loop_ll), nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<List<T1>>::Cons>((*_write)->v_mut()).a1;
          _loop_ll = tails(_loop_ll);
          _loop_fuel = f;
          continue;
        }
      }
    }
    return std::move(*_head);
  }

  template <typename T1>
  static List<List<T1>> transpose(const List<List<T1>> &ll) {
    return transpose_fuel<T1>(100u, ll);
  }

  /// collatz_list n generates collatz sequence.
  static List<unsigned int> collatz_list_fuel(unsigned int fuel,
                                              unsigned int n);
  static List<unsigned int> collatz_list(unsigned int n);
  /// run_sum l running sum (scanl for addition).
  static List<unsigned int> run_sum_aux(unsigned int acc,
                                        const List<unsigned int> &l);
  static List<unsigned int> run_sum(const List<unsigned int> &l);
  /// rotate_left n l rotates list left by n positions.
  static List<unsigned int> rotate_left_fuel(unsigned int fuel, unsigned int n,
                                             List<unsigned int> l);
  static List<unsigned int> rotate_left(unsigned int n,
                                        const List<unsigned int> &l);

  /// iterate f n x generates x, f x, f (f x), ... of length n.
  template <typename F0>
    requires std::is_invocable_r_v<unsigned int, F0 &, unsigned int &>
  static List<unsigned int> iterate(F0 &&f, unsigned int n, unsigned int x) {
    std::unique_ptr<List<unsigned int>> _head{};
    std::unique_ptr<List<unsigned int>> *_write = &_head;
    unsigned int _loop_x = std::move(x);
    unsigned int _loop_n = std::move(n);
    while (true) {
      if (_loop_n <= 0) {
        *_write =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        unsigned int m = _loop_n - 1;
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(_loop_x, nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut()).a1;
        _loop_x = f(_loop_x);
        _loop_n = m;
        continue;
      }
    }
    return std::move(*_head);
  }

  /// sum_acc acc l sum with accumulator.
  static unsigned int sum_acc(unsigned int acc, const List<unsigned int> &l);
  /// repeat_string s n repeats string n times (using list as string).
  static List<unsigned int> repeat_string(const List<unsigned int> &s,
                                          unsigned int n);
  /// repeat_with_sep s sep n repeats with separator.
  static List<unsigned int> repeat_with_sep(List<unsigned int> s,
                                            const List<unsigned int> &sep,
                                            unsigned int n);
  /// string_chain s n recursive string chain: s-chain(s, n-1)-end.
  static List<unsigned int>
  string_chain_fuel(unsigned int fuel, const List<unsigned int> &s,
                    unsigned int n, const List<unsigned int> &sep,
                    const List<unsigned int> &end_marker);
  static List<unsigned int> string_chain(const List<unsigned int> &s,
                                         unsigned int n,
                                         const List<unsigned int> &sep,
                                         const List<unsigned int> &end_marker);
  /// split_by_sign l base pos neg splits list based on base threshold.
  static std::pair<List<unsigned int>, List<unsigned int>>
  split_by_sign(const List<unsigned int> &l, unsigned int base,
                List<unsigned int> pos, List<unsigned int> neg);
  /// differences l computes differences between consecutive elements.
  static List<unsigned int> differences(const List<unsigned int> &l);
  /// replace_at idx value l replaces element at index with value.
  static List<unsigned int> replace_at(unsigned int idx, unsigned int value,
                                       const List<unsigned int> &l);
  /// cycle n l repeats list n times.
  static List<unsigned int> cycle(unsigned int n, const List<unsigned int> &l);
  /// Helper: get first element.
  static unsigned int first_elem(const List<unsigned int> &l);
  /// Helper: get last element.
  static unsigned int last_elem(const List<unsigned int> &l);
  /// Helper: remove first element.
  static List<unsigned int> tail_list(const List<unsigned int> &l);
  /// Helper: remove last element.
  static List<unsigned int> init_list(const List<unsigned int> &l);
  /// is_palindrome s checks if list is a palindrome.
  static bool is_palindrome_fuel(unsigned int fuel,
                                 const List<unsigned int> &s);
  static bool is_palindrome(const List<unsigned int> &s);
  /// string_subsequences s generates all subsequences treating list as string.
  static List<List<unsigned int>>
  string_subsequences(const List<unsigned int> &s);
  /// run_length_groups l groups consecutive runs into sublist lengths.
  static List<unsigned int> run_length_groups_aux(unsigned int prev,
                                                  unsigned int count,
                                                  const List<unsigned int> &l);
  static List<unsigned int> run_length_groups(const List<unsigned int> &l);
  /// is_prefix_of l1 l2 checks if l1 is a prefix of l2.
  static bool is_prefix_of(const List<unsigned int> &l1,
                           const List<unsigned int> &l2);
  /// lis l longest increasing subsequence (greedy, not optimal).
  static List<unsigned int> lis(List<unsigned int> l);

  /// take_while p l takes elements while predicate holds.
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, unsigned int &>
  static List<unsigned int> take_while(F0 &&p, const List<unsigned int> &l) {
    std::unique_ptr<List<unsigned int>> _head{};
    std::unique_ptr<List<unsigned int>> *_write = &_head;
    const List<unsigned int> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v())) {
        *_write =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l->v());
        if (p(a0)) {
          auto _cell = std::make_unique<List<unsigned int>>(
              typename List<unsigned int>::Cons(a0, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                   .a1;
          _loop_l = a1.get();
          continue;
        } else {
          *_write =
              std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
          break;
        }
      }
    }
    return std::move(*_head);
  }

  /// drop_while p l drops elements while predicate holds.
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, unsigned int &>
  static List<unsigned int> drop_while(F0 &&p, const List<unsigned int> &l) {
    List<unsigned int> _result;
    const List<unsigned int> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v())) {
        _result = List<unsigned int>::nil();
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l->v());
        if (p(a0)) {
          _loop_l = a1.get();
        } else {
          _result = List<unsigned int>::cons(a0, *a1);
          break;
        }
      }
    }
    return _result;
  }

  /// Helper: check if element is in list.
  static bool elem(unsigned int x, const List<unsigned int> &l);
  /// Helper: filter list.
  static List<unsigned int> filter_ne(unsigned int x,
                                      const List<unsigned int> &l);
  /// nub l removes duplicates from list.
  static List<unsigned int> nub_fuel(unsigned int fuel,
                                     const List<unsigned int> &l);
  static List<unsigned int> nub(const List<unsigned int> &l);
  /// group l groups consecutive equal elements.
  static List<List<unsigned int>> group_fuel(unsigned int fuel,
                                             const List<unsigned int> &l);
  static List<List<unsigned int>> group(const List<unsigned int> &l);
  /// Helper: get head with default.
  static unsigned int head_or(unsigned int default0,
                              const List<unsigned int> &l);
  /// remove_if_sum_even l removes elements where sum with next is even.
  static List<unsigned int> remove_if_sum_even(const List<unsigned int> &l);

  /// bool_all p l checks if all elements satisfy predicate (forall with &&).
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, unsigned int &>
  static bool bool_all(
      F0 &&p,
      const List<unsigned int>
          &l) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      const List<unsigned int> *l;
    };

    /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
    struct _Resume_Cons {
      bool a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    bool _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified bool_all: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<unsigned int> &l = *_f.l;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = true;
        } else {
          const auto &[a0, a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{p(a0)});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = (_f.a0 && _result);
      }
    }
    return _result;
  }

  /// run_length_encode l encodes consecutive runs: 1,1,2,2,2 -> (1,2),(2,3).
  static List<std::pair<unsigned int, unsigned int>>
  run_length_encode_fuel(unsigned int fuel, const List<unsigned int> &l);
  static List<std::pair<unsigned int, unsigned int>>
  run_length_encode(const List<unsigned int> &l);
  /// between lo hi l filters elements in range lo, hi.
  static List<unsigned int> between(unsigned int lo, unsigned int hi,
                                    const List<unsigned int> &l);
};

#endif // INCLUDED_LOOPIFY_SEQUENCES
