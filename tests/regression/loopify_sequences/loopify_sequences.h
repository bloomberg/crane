#ifndef INCLUDED_LOOPIFY_SEQUENCES
#define INCLUDED_LOOPIFY_SEQUENCES

#include <any>
#include <memory>
#include <type_traits>
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
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        _drain(_cur->v_mut());
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  uint64_t length() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return (a1->length() + 1);
    }
  }

  List<A> app(List<A> m) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return m;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return List<A>::cons(a0, a1->app(std::move(m)));
    }
  }
};

struct LoopifySequences {
  /// alternate_sum sign acc l alternating sum with sign flip.
  static uint64_t alternate_sum(uint64_t sign, uint64_t acc,
                                const List<uint64_t> &l);

  /// intercalate sep lists inserts sep between lists and flattens.
  template <typename T1>
  static List<T1> intercalate(
      const List<T1> &sep,
      const List<List<T1>> &lists) { /// _Enter: captures varying parameters for
                                     /// each recursive call.

    struct _Enter {
      const List<List<T1>> *lists;
    };

    /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
    struct _Resume_Cons {
      List<T1> a0;
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
            _stack.emplace_back(_Resume_Cons{a0});
            _stack.emplace_back(_Enter{a1.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = std::move(_f.a0).app(sep.app(std::move(_result)));
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
  }

  /// transpose l transposes a list of lists.
  template <typename T1>
  static List<List<T1>> transpose_fuel(
      uint64_t fuel,
      const List<List<T1>> &
          ll) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      List<List<T1>> ll;
      uint64_t fuel;
    };

    /// _Resume1: saves [_s0], resumes after recursive call with _result.
    struct _Resume1 {
      List<T1> _s0;
    };

    using _Frame = std::variant<_Enter, _Resume1>;
    List<List<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{ll, fuel});
    /// Loopified transpose_fuel: _Enter -> _Resume1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<List<T1>> &ll = std::move(_f.ll);
        uint64_t fuel = _f.fuel;
        if (fuel <= 0) {
          _result = List<List<T1>>::nil();
        } else {
          uint64_t f = fuel - 1;
          auto all_nil_impl = [](auto &, const List<List<T1>> &l) -> bool {
            const List<List<T1>> *_loop_l = &l;
            while (true) {
              if (std::holds_alternative<typename List<List<T1>>::Nil>(
                      _loop_l->v())) {
                return true;
              } else {
                const auto &[a0, a1] =
                    std::get<typename List<List<T1>>::Cons>(_loop_l->v());
                if (std::holds_alternative<typename List<T1>::Nil>(a0.v())) {
                  _loop_l = a1.get();
                } else {
                  return false;
                }
              }
            }
          };
          auto all_nil = [&](const List<List<T1>> &l) -> bool {
            return all_nil_impl(all_nil_impl, l);
          };
          if (all_nil(ll)) {
            _result = List<List<T1>>::nil();
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
            _stack.emplace_back(_Resume1{std::move(heads(ll))});
            _stack.emplace_back(_Enter{tails(ll), f});
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume1>(_frame));
        _result = List<List<T1>>::cons(std::move(_f._s0), std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1>
  static List<List<T1>> transpose(const List<List<T1>> &ll) {
    return transpose_fuel<T1>(UINT64_C(100), ll);
  }

  /// collatz_list n generates collatz sequence.
  static List<uint64_t> collatz_list_fuel(uint64_t fuel, uint64_t n);
  static List<uint64_t> collatz_list(uint64_t n);
  /// run_sum l running sum (scanl for addition).
  static List<uint64_t> run_sum_aux(uint64_t acc, const List<uint64_t> &l);
  static List<uint64_t> run_sum(const List<uint64_t> &l);
  /// rotate_left n l rotates list left by n positions.
  static List<uint64_t> rotate_left_fuel(uint64_t fuel, uint64_t n,
                                         List<uint64_t> l);
  static List<uint64_t> rotate_left(uint64_t n, const List<uint64_t> &l);

  /// iterate f n x generates x, f x, f (f x), ... of length n.
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static List<uint64_t>
  iterate(F0 &&f, uint64_t n,
          uint64_t x) { /// _Enter: captures varying parameters for each
                        /// recursive call.

    struct _Enter {
      uint64_t x;
      uint64_t n;
    };

    /// _Resume_m: saves [x], resumes after recursive call with _result.
    struct _Resume_m {
      uint64_t x;
    };

    using _Frame = std::variant<_Enter, _Resume_m>;
    List<uint64_t> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{x, n});
    /// Loopified iterate: _Enter -> _Resume_m.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        uint64_t x = _f.x;
        uint64_t n = _f.n;
        if (n <= 0) {
          _result = List<uint64_t>::nil();
        } else {
          uint64_t m = n - 1;
          _stack.emplace_back(_Resume_m{x});
          _stack.emplace_back(_Enter{f(x), m});
        }
      } else {
        auto _f = std::move(std::get<_Resume_m>(_frame));
        _result = List<uint64_t>::cons(_f.x, std::move(_result));
      }
    }
    return _result;
  }

  /// sum_acc acc l sum with accumulator.
  static uint64_t sum_acc(uint64_t acc, const List<uint64_t> &l);
  /// repeat_string s n repeats string n times (using list as string).
  static List<uint64_t> repeat_string(const List<uint64_t> &s, uint64_t n);
  /// repeat_with_sep s sep n repeats with separator.
  static List<uint64_t> repeat_with_sep(List<uint64_t> s,
                                        const List<uint64_t> &sep, uint64_t n);
  /// string_chain s n recursive string chain: s-chain(s, n-1)-end.
  static List<uint64_t> string_chain_fuel(uint64_t fuel,
                                          const List<uint64_t> &s, uint64_t n,
                                          const List<uint64_t> &sep,
                                          const List<uint64_t> &end_marker);
  static List<uint64_t> string_chain(const List<uint64_t> &s, uint64_t n,
                                     const List<uint64_t> &sep,
                                     const List<uint64_t> &end_marker);
  /// split_by_sign l base pos neg splits list based on base threshold.
  static std::pair<List<uint64_t>, List<uint64_t>>
  split_by_sign(const List<uint64_t> &l, uint64_t base, List<uint64_t> pos,
                List<uint64_t> neg);
  /// differences l computes differences between consecutive elements.
  static List<uint64_t> differences(const List<uint64_t> &l);
  /// replace_at idx value l replaces element at index with value.
  static List<uint64_t> replace_at(uint64_t idx, uint64_t value,
                                   const List<uint64_t> &l);
  /// cycle n l repeats list n times.
  static List<uint64_t> cycle(uint64_t n, const List<uint64_t> &l);
  /// Helper: get first element.
  static uint64_t first_elem(const List<uint64_t> &l);
  /// Helper: get last element.
  static uint64_t last_elem(const List<uint64_t> &l);
  /// Helper: remove first element.
  static List<uint64_t> tail_list(const List<uint64_t> &l);
  /// Helper: remove last element.
  static List<uint64_t> init_list(const List<uint64_t> &l);
  /// is_palindrome s checks if list is a palindrome.
  static bool is_palindrome_fuel(uint64_t fuel, const List<uint64_t> &s);
  static bool is_palindrome(const List<uint64_t> &s);
  /// string_subsequences s generates all subsequences treating list as string.
  static List<List<uint64_t>> string_subsequences(const List<uint64_t> &s);
  /// run_length_groups l groups consecutive runs into sublist lengths.
  static List<uint64_t> run_length_groups_aux(uint64_t prev, uint64_t count,
                                              const List<uint64_t> &l);
  static List<uint64_t> run_length_groups(const List<uint64_t> &l);
  /// is_prefix_of l1 l2 checks if l1 is a prefix of l2.
  static bool is_prefix_of(const List<uint64_t> &l1, const List<uint64_t> &l2);
  /// lis l longest increasing subsequence (greedy, not optimal).
  static List<uint64_t> lis(List<uint64_t> l);

  /// take_while p l takes elements while predicate holds.
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static List<uint64_t>
  take_while(F0 &&p,
             const List<uint64_t> &l) { /// _Enter: captures varying parameters
                                        /// for each recursive call.

    struct _Enter {
      const List<uint64_t> *l;
    };

    /// _Resume1: saves [a0], resumes after recursive call with _result.
    struct _Resume1 {
      uint64_t a0;
    };

    using _Frame = std::variant<_Enter, _Resume1>;
    List<uint64_t> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified take_while: _Enter -> _Resume1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = List<uint64_t>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          if (p(a0)) {
            _stack.emplace_back(_Resume1{a0});
            _stack.emplace_back(_Enter{a1.get()});
          } else {
            _result = List<uint64_t>::nil();
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume1>(_frame));
        _result = List<uint64_t>::cons(_f.a0, std::move(_result));
      }
    }
    return _result;
  }

  /// drop_while p l drops elements while predicate holds.
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static List<uint64_t> drop_while(F0 &&p, const List<uint64_t> &l) {
    const List<uint64_t> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        return List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        if (p(a0)) {
          _loop_l = a1.get();
        } else {
          return List<uint64_t>::cons(a0, *a1);
        }
      }
    }
  }

  /// Helper: check if element is in list.
  static bool elem(uint64_t x, const List<uint64_t> &l);
  /// Helper: filter list.
  static List<uint64_t> filter_ne(uint64_t x, const List<uint64_t> &l);
  /// nub l removes duplicates from list.
  static List<uint64_t> nub_fuel(uint64_t fuel, const List<uint64_t> &l);
  static List<uint64_t> nub(const List<uint64_t> &l);
  /// group l groups consecutive equal elements.
  static List<List<uint64_t>> group_fuel(uint64_t fuel,
                                         const List<uint64_t> &l);
  static List<List<uint64_t>> group(const List<uint64_t> &l);
  /// Helper: get head with default.
  static uint64_t head_or(uint64_t default0, const List<uint64_t> &l);
  /// remove_if_sum_even l removes elements where sum with next is even.
  static List<uint64_t> remove_if_sum_even(const List<uint64_t> &l);

  /// bool_all p l checks if all elements satisfy predicate (forall with &&).
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static bool
  bool_all(F0 &&p,
           const List<uint64_t> &l) { /// _Enter: captures varying parameters
                                      /// for each recursive call.

    struct _Enter {
      const List<uint64_t> *l;
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
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = true;
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{p(a0)});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = (_f.a0 && std::move(_result));
      }
    }
    return _result;
  }

  /// run_length_encode l encodes consecutive runs: 1,1,2,2,2 -> (1,2),(2,3).
  static List<std::pair<uint64_t, uint64_t>>
  run_length_encode_fuel(uint64_t fuel, const List<uint64_t> &l);
  static List<std::pair<uint64_t, uint64_t>>
  run_length_encode(const List<uint64_t> &l);
  /// between lo hi l filters elements in range lo, hi.
  static List<uint64_t> between(uint64_t lo, uint64_t hi,
                                const List<uint64_t> &l);
};

#endif // INCLUDED_LOOPIFY_SEQUENCES
