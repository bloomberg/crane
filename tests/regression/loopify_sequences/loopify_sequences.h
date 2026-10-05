#ifndef INCLUDED_LOOPIFY_SEQUENCES
#define INCLUDED_LOOPIFY_SEQUENCES

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
      : v_(crane_convert_spine(
            _other, std::shared_ptr<List<A>>(nullptr),
            [](const List<CraneU> &_cell) -> const List<CraneU> * {
              if (std::holds_alternative<typename List<CraneU>::Cons>(
                      _cell.v())) {
                return std::get<typename List<CraneU>::Cons>(_cell.v()).l.get();
              } else {
                return nullptr;
              }
            },
            [&](const List<CraneU> &_other,
                std::shared_ptr<List<A>> _below) -> variant_t {
              if (std::holds_alternative<typename List<CraneU>::Nil>(
                      _other.v())) {
                return Nil{};
              } else {
                const auto &[a, l] =
                    std::get<typename List<CraneU>::Cons>(_other.v());
                return Cons{
                    [&]() -> A {
                      if constexpr (crane_convertible<A, const CraneU &>) {
                        return crane_convert<A>(a);
                      } else {
                        throw std::logic_error(
                            "unreachable: inactive constructor field at this "
                            "instantiation");
                      }
                    }(),
                    std::move(_below)};
              }
            },
            [](auto &&_alt) {
              return std::make_shared<List<A>>(std::move(_alt));
            })) {}

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

  uint64_t length() const {
    const List<A> *_self = this;

    /// CraneEnter: captures varying parameters for each recursive call.
    struct CraneEnter {
      const List<A> *_self;
    };

    /// CraneCont_Cons: resumes after recursive call, then processes rest.
    struct CraneCont_Cons {};

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    uint64_t _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{_self});
    /// Loopified length: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(CraneCont_Cons{});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }

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

struct LoopifySequences {
  /// alternate_sum sign acc l alternating sum with sign flip.
  static uint64_t alternate_sum(uint64_t sign, uint64_t acc,
                                const List<uint64_t> &l);

  /// intercalate sep lists inserts sep between lists and flattens.
  template <typename T1>
  static List<T1> intercalate(
      const List<T1> &sep,
      const List<List<T1>> &lists) { /// CraneEnter: captures varying parameters
                                     /// for each recursive call.

    struct CraneEnter {
      const List<List<T1>> *lists;
    };

    /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_Cons {
      List<T1> a0;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    List<T1> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&lists});
    /// Loopified intercalate: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
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
            _stack.emplace_back(CraneCont_Cons{a0});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        List<T1> a0 = std::move(_f.a0);
        _result = a0.app(sep.app(std::move(_result)));
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
      auto go = [&](const List<T1> &rest) -> List<T1> {
        /// CraneEnter: captures varying parameters for each recursive call.
        struct CraneEnter {
          const List<T1> *rest;
        };
        /// CraneCont_Cons: saves [a00, sep], resumes after recursive call, then
        /// processes rest.
        struct CraneCont_Cons {
          T1 a00;
          T1 sep;
        };
        using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
        List<T1> _result{};
        crane::small_vector<CraneFrame> _stack;
        _stack.emplace_back(CraneEnter{&rest});
        /// Loopified go: CraneEnter -> CraneCont_Cons.
        while (!_stack.empty()) {
          CraneFrame _frame = std::move(_stack.back());
          _stack.pop_back();
          if (std::holds_alternative<CraneEnter>(_frame)) {
            auto _f = std::move(std::get<CraneEnter>(_frame));
            const List<T1> &rest = *_f.rest;
            if (std::holds_alternative<typename List<T1>::Nil>(rest.v())) {
              _result = List<T1>::nil();
            } else {
              const auto &[a00, a10] =
                  std::get<typename List<T1>::Cons>(rest.v());
              _stack.emplace_back(CraneCont_Cons{a00, sep});
              _stack.emplace_back(CraneEnter{crane_raw(a10)});
            }
          } else {
            auto _f = std::move(std::get<CraneCont_Cons>(_frame));
            auto a00 = std::move(_f.a00);
            auto sep = std::move(_f.sep);
            _result =
                List<T1>::cons(sep, List<T1>::cons(a00, std::move(_result)));
          }
        }
        return _result;
      };
      return List<T1>::cons(a0, go(*a1));
    }
  }

  /// transpose l transposes a list of lists.
  template <typename T1>
  static List<List<T1>> transpose_fuel(uint64_t fuel,
                                       const List<List<T1>> &ll) {
    std::optional<List<List<T1>>> _root{};
    std::shared_ptr<List<List<T1>>> *_write = nullptr;
    List<List<T1>> _loop_ll = ll;
    uint64_t _loop_fuel = fuel;
    while (true) {
      if (_loop_fuel <= 0) {
        auto _value = List<List<T1>>::nil();
        (_write
             ? *(*_write = std::make_shared<List<List<T1>>>(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        uint64_t f = _loop_fuel - 1;
        auto all_nil = [](const List<List<T1>> &l) -> bool {
          const List<List<T1>> *_loop_l = &l;
          while (true) {
            if (std::holds_alternative<typename List<List<T1>>::Nil>(
                    _loop_l->v())) {
              return true;
            } else {
              const auto &[a0, a1] =
                  std::get<typename List<List<T1>>::Cons>(_loop_l->v());
              if (std::holds_alternative<typename List<T1>::Nil>(a0.v())) {
                _loop_l = crane_raw(a1);
              } else {
                return false;
              }
            }
          }
        };
        if (all_nil(_loop_ll)) {
          auto _value = List<List<T1>>::nil();
          (_write ? *(*_write =
                          std::make_shared<List<List<T1>>>(std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          auto heads = [&](const List<List<T1>> &l) -> List<T1> {
            /// CraneEnter: captures varying parameters for each recursive call.
            struct CraneEnter {
              const List<List<T1>> *l;
            };
            /// CraneCont_Cons: saves [a01], resumes after recursive call, then
            /// processes rest.
            struct CraneCont_Cons {
              T1 a01;
            };
            using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
            List<T1> _result{};
            crane::small_vector<CraneFrame> _stack;
            _stack.emplace_back(CraneEnter{&l});
            /// Loopified heads: CraneEnter -> CraneCont_Cons.
            while (!_stack.empty()) {
              CraneFrame _frame = std::move(_stack.back());
              _stack.pop_back();
              if (std::holds_alternative<CraneEnter>(_frame)) {
                auto _f = std::move(std::get<CraneEnter>(_frame));
                const List<List<T1>> &l = *_f.l;
                if (std::holds_alternative<typename List<List<T1>>::Nil>(
                        l.v())) {
                  _result = List<T1>::nil();
                } else {
                  const auto &[a00, a10] =
                      std::get<typename List<List<T1>>::Cons>(l.v());
                  if (std::holds_alternative<typename List<T1>::Nil>(a00.v())) {
                    _stack.emplace_back(CraneEnter{crane_raw(a10)});
                  } else {
                    const auto &[a01, a11] =
                        std::get<typename List<T1>::Cons>(a00.v());
                    _stack.emplace_back(CraneCont_Cons{a01});
                    _stack.emplace_back(CraneEnter{crane_raw(a10)});
                  }
                }
              } else {
                auto _f = std::move(std::get<CraneCont_Cons>(_frame));
                auto a01 = std::move(_f.a01);
                _result = List<T1>::cons(a01, std::move(_result));
              }
            }
            return _result;
          };
          auto tails = [&](const List<List<T1>> &l) -> List<List<T1>> {
            /// CraneEnter: captures varying parameters for each recursive call.
            struct CraneEnter {
              const List<List<T1>> *l;
            };
            /// CraneCont_Cons: saves [a12], resumes after recursive call, then
            /// processes rest.
            struct CraneCont_Cons {
              std::shared_ptr<List<T1>> a12;
            };
            using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
            List<List<T1>> _result{};
            crane::small_vector<CraneFrame> _stack;
            _stack.emplace_back(CraneEnter{&l});
            /// Loopified tails: CraneEnter -> CraneCont_Cons.
            while (!_stack.empty()) {
              CraneFrame _frame = std::move(_stack.back());
              _stack.pop_back();
              if (std::holds_alternative<CraneEnter>(_frame)) {
                auto _f = std::move(std::get<CraneEnter>(_frame));
                const List<List<T1>> &l = *_f.l;
                if (std::holds_alternative<typename List<List<T1>>::Nil>(
                        l.v())) {
                  _result = List<List<T1>>::nil();
                } else {
                  const auto &[a01, a11] =
                      std::get<typename List<List<T1>>::Cons>(l.v());
                  if (std::holds_alternative<typename List<T1>::Nil>(a01.v())) {
                    _stack.emplace_back(CraneEnter{crane_raw(a11)});
                  } else {
                    const auto &[a02, a12] =
                        std::get<typename List<T1>::Cons>(a01.v());
                    _stack.emplace_back(CraneCont_Cons{a12});
                    _stack.emplace_back(CraneEnter{crane_raw(a11)});
                  }
                }
              } else {
                auto _f = std::move(std::get<CraneCont_Cons>(_frame));
                std::shared_ptr<List<T1>> a12 = std::move(_f.a12);
                _result = List<List<T1>>::cons(*a12, std::move(_result));
              }
            }
            return _result;
          };
          auto _cell = typename List<List<T1>>::Cons(heads(_loop_ll), nullptr);
          List<List<T1>> &_node =
              (_write ? *(*_write = std::make_shared<List<List<T1>>>(
                              std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write = &std::get<typename List<List<T1>>::Cons>(_node.v_mut()).l;
          _loop_ll = tails(_loop_ll);
          _loop_fuel = f;
          continue;
        }
      }
    }
    return std::move(*_root);
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
  static List<uint64_t> iterate(F0 &&f, uint64_t n, uint64_t x) {
    std::optional<List<uint64_t>> _root{};
    std::shared_ptr<List<uint64_t>> *_write = nullptr;
    uint64_t _loop_x = x;
    uint64_t _loop_n = n;
    while (true) {
      if (_loop_n <= 0) {
        auto _value = List<uint64_t>::nil();
        (_write
             ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        uint64_t m = _loop_n - 1;
        auto _cell = typename List<uint64_t>::Cons(_loop_x, nullptr);
        List<uint64_t> &_node =
            (_write ? *(*_write =
                            std::make_shared<List<uint64_t>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
        _loop_x = f(_loop_x);
        _loop_n = m;
        continue;
      }
    }
    return std::move(*_root);
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
  split_by_sign(const List<uint64_t> &l, uint64_t base,
                const List<uint64_t> &pos, const List<uint64_t> &neg);
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
  static List<uint64_t> take_while(F0 &&p, const List<uint64_t> &l) {
    std::optional<List<uint64_t>> _root{};
    std::shared_ptr<List<uint64_t>> *_write = nullptr;
    const List<uint64_t> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        auto _value = List<uint64_t>::nil();
        (_write
             ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        if (p(a0)) {
          auto _cell = typename List<uint64_t>::Cons(a0, nullptr);
          List<uint64_t> &_node =
              (_write ? *(*_write = std::make_shared<List<uint64_t>>(
                              std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
          _loop_l = crane_raw(a1);
          continue;
        } else {
          auto _value = List<uint64_t>::nil();
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        }
      }
    }
    return std::move(*_root);
  }

  /// drop_while p l drops elements while predicate holds.
  template <typename F0>
  static List<uint64_t> drop_while(F0 &&p, const List<uint64_t> &l) {
    const List<uint64_t> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        return List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        if (p(a0)) {
          _loop_l = crane_raw(a1);
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
           const List<uint64_t> &l) { /// CraneEnter: captures varying
                                      /// parameters for each recursive call.

    struct CraneEnter {
      const List<uint64_t> *l;
    };

    /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_Cons {
      uint64_t a0;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    bool _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified bool_all: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = true;
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          _stack.emplace_back(CraneCont_Cons{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        uint64_t a0 = _f.a0;
        _result = (p(a0) && std::move(_result));
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
