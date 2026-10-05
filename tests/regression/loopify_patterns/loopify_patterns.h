#ifndef INCLUDED_LOOPIFY_PATTERNS
#define INCLUDED_LOOPIFY_PATTERNS

#include "crane_fn.h"
#include "fn.h"
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

/// Complex control flow and pattern matching edge cases.
struct LoopifyPatterns {
  template <typename A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      A a;
      std::shared_ptr<list<A>> l;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    list() {}

    explicit list(Nil _v) : v_(_v) {}

    explicit list(Cons _v) : v_(std::move(_v)) {}

    template <typename CraneU>
    list(const list<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename list<CraneU>::Nil>(
                    _other.v())) {
              return Nil{};
            } else {
              const auto &[a, l] =
                  std::get<typename list<CraneU>::Cons>(_other.v());
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
                  (l ? std::make_shared<list<A>>(crane_convert<list<A>>(*l))
                     : nullptr)};
            }
          }()) {}

    static list<A> nil() { return list<A>(Nil{}); }

    static list<A> cons(A a, list<A> l) {
      return list<A>(
          Cons{std::move(a), std::make_shared<list<A>>(std::move(l))});
    }

    // MANIPULATORS
    ~list() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<list<A>> {
        if (auto *_alt = std::get_if<Cons>(&_v)) {
          if (_alt->l && _alt->l.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->l);
          }
        }
        return nullptr;
      };
      std::shared_ptr<list<A>> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    list(const list &) = default;
    list &operator=(const list &) = default;
    list(list &&) = default;
    list &operator=(list &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F1>
  static T2
  list_rect(T2 f, F1 &&f0,
            const list<T1> &l) { /// CraneEnter: captures varying parameters for
                                 /// each recursive call.

    struct CraneEnter {
      const list<T1> *l;
    };

    /// CraneCont_Cons: saves [a0, a1], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Cons {
      T1 a0;
      std::shared_ptr<list<T1>> a1;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    T2 _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified list_rect: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const list<T1> &l = *_f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = f;
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
          _stack.emplace_back(CraneCont_Cons{a0, a1});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        auto a0 = std::move(_f.a0);
        std::shared_ptr<list<T1>> a1 = std::move(_f.a1);
        _result = f0(a0, *a1, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename F1>
  static T2
  list_rec(T2 f, F1 &&f0,
           const list<T1> &l) { /// CraneEnter: captures varying parameters for
                                /// each recursive call.

    struct CraneEnter {
      const list<T1> *l;
    };

    /// CraneCont_Cons: saves [a0, a1], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Cons {
      T1 a0;
      std::shared_ptr<list<T1>> a1;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    T2 _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified list_rec: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const list<T1> &l = *_f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = f;
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
          _stack.emplace_back(CraneCont_Cons{a0, a1});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        auto a0 = std::move(_f.a0);
        std::shared_ptr<list<T1>> a1 = std::move(_f.a1);
        _result = f0(a0, *a1, std::move(_result));
      }
    }
    return _result;
  }

  /// multi_let n multiple sequential let bindings before recursion.
  static uint64_t multi_let(uint64_t n);
  /// nested_if n deeply nested if-then-else with recursion at different depths.
  static uint64_t nested_if_fuel(uint64_t fuel, uint64_t n);
  static uint64_t nested_if(uint64_t n);
  /// deep_nest n deeply nested function application.
  static uint64_t deep_nest(uint64_t n);
  /// bool_chain n target multiple recursive calls in || chain.
  static bool bool_chain_fuel(uint64_t fuel, uint64_t n, uint64_t target);
  static bool bool_chain(uint64_t n, uint64_t target);
  /// chained_comp n boolean result with double recursion.
  static bool chained_comp(uint64_t n);
  /// tuple_constr n recursive calls in multiple tuple positions.
  static std::pair<std::pair<uint64_t, uint64_t>, uint64_t>
  tuple_constr(uint64_t n);
  /// sum_prod_count l a_sum a_prod a_count multiple accumulator updates.
  static std::pair<std::pair<uint64_t, uint64_t>, uint64_t>
  sum_prod_count(const list<uint64_t> &l, uint64_t a_sum, uint64_t a_prod,
                 uint64_t a_count);
  /// split_by_sign l pos neg partition with dual accumulators.
  static std::pair<list<uint64_t>, list<uint64_t>>
  split_by_sign_aux(const list<uint64_t> &l, uint64_t base,
                    const list<uint64_t> &pos, const list<uint64_t> &neg);
  static std::pair<list<uint64_t>, list<uint64_t>>
  split_by_sign(const list<uint64_t> &l, uint64_t base);
  /// guard_accum acc l multiple when-style guards with different logic.
  static uint64_t guard_accum(uint64_t acc, const list<uint64_t> &l);
  /// cons_computed n l cons with conditional parameter change.
  static list<uint64_t> cons_computed(uint64_t n, const list<uint64_t> &l);
  /// mod_pattern n recursive call in mod expression.
  static uint64_t mod_pattern(uint64_t n);
  /// alternating_ops n alternating operations based on modulo.
  static uint64_t alternating_ops(uint64_t n);

  /// max_by f l recursive max with function application.
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, const uint64_t &> &&
             std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static uint64_t
  max_by(F0 &&f,
         const list<uint64_t> &l) { /// CraneEnter: captures varying parameters
                                    /// for each recursive call.

    struct CraneEnter {
      const list<uint64_t> *l;
    };

    /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_Cons {
      uint64_t a0;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    uint64_t _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified max_by: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const list<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename list<uint64_t>::Nil>(l.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename list<uint64_t>::Cons>(l.v());
          auto &&_sv = *a1;
          if (std::holds_alternative<typename list<uint64_t>::Nil>(_sv.v())) {
            _result = f(a0);
          } else {
            _stack.emplace_back(CraneCont_Cons{a0});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        uint64_t a0 = _f.a0;
        uint64_t rest_max = std::move(_result);
        uint64_t fx = f(a0);
        if (fx < rest_max) {
          _result = std::move(rest_max);
        } else {
          _result = std::move(fx);
        }
      }
    }
    return _result;
  }

  /// replace_at idx value l replace element at index.
  static list<uint64_t> replace_at(uint64_t idx, uint64_t value,
                                   const list<uint64_t> &l);
  /// nested_pattern l three-element tuple pattern.
  static uint64_t nested_pattern(
      const list<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>> &l);
  /// let_nested n let with nested let in binding.
  static uint64_t let_nested(uint64_t n);

  /// insert_everywhere x l insert element at all possible positions.
  template <typename T1>
  static list<list<T1>>
  insert_everywhere(const T1 &x,
                    const list<T1> &l) { /// CraneEnter: captures varying
                                         /// parameters for each recursive call.

    struct CraneEnter {
      const list<T1> *l;
    };

    /// CraneCont_Cons: saves [a0, a1, map_cons_h], resumes after recursive
    /// call, then processes rest.
    struct CraneCont_Cons {
      T1 a0;
      std::shared_ptr<list<T1>> a1;
      crane::fn<list<list<T1>>(list<list<T1>>)> map_cons_h;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    list<list<T1>> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified insert_everywhere: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const list<T1> &l = *_f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = list<list<T1>>::cons(list<T1>::cons(x, list<T1>::nil()),
                                         list<list<T1>>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
          auto map_cons_h = [&](const list<list<T1>> &lsts) -> list<list<T1>> {
            /// CraneEnter: captures varying parameters for each recursive call.
            struct CraneEnter {
              const list<list<T1>> *lsts;
            };
            /// CraneCont_Cons: saves [a0, a00], resumes after recursive call,
            /// then processes rest.
            struct CraneCont_Cons {
              std::decay_t<decltype(a0)> a0;
              list<T1> a00;
            };
            using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
            list<list<T1>> _result{};
            crane::small_vector<CraneFrame> _stack;
            _stack.emplace_back(CraneEnter{&lsts});
            /// Loopified map_cons_h: CraneEnter -> CraneCont_Cons.
            while (!_stack.empty()) {
              CraneFrame _frame = std::move(_stack.back());
              _stack.pop_back();
              if (std::holds_alternative<CraneEnter>(_frame)) {
                auto _f = std::move(std::get<CraneEnter>(_frame));
                const list<list<T1>> &lsts = *_f.lsts;
                if (std::holds_alternative<typename list<list<T1>>::Nil>(
                        lsts.v())) {
                  _result = list<list<T1>>::nil();
                } else {
                  const auto &[a00, a10] =
                      std::get<typename list<list<T1>>::Cons>(lsts.v());
                  _stack.emplace_back(CraneCont_Cons{a0, a00});
                  _stack.emplace_back(CraneEnter{crane_raw(a10)});
                }
              } else {
                auto _f = std::move(std::get<CraneCont_Cons>(_frame));
                a0 = _f.a0;
                list<T1> a00 = std::move(_f.a00);
                _result = list<list<T1>>::cons(list<T1>::cons(a0, a00),
                                               std::move(_result));
              }
            }
            return _result;
          };
          _stack.emplace_back(CraneCont_Cons{a0, a1, std::move(map_cons_h)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        auto a0 = std::move(_f.a0);
        std::shared_ptr<list<T1>> a1 = std::move(_f.a1);
        crane::fn<list<list<T1>>(list<list<T1>>)> map_cons_h =
            std::move(_f.map_cons_h);
        _result =
            list<list<T1>>::cons(list<T1>::cons(x, list<T1>::cons(a0, *a1)),
                                 map_cons_h(std::move(_result)));
      }
    }
    return _result;
  }

  /// Helper: list length.
  static uint64_t list_len(const list<uint64_t> &l);

  /// merge_by cmp l1 l2 merge with custom comparator.
  template <typename F1>
  static list<uint64_t> merge_by_fuel(uint64_t fuel, F1 &&cmp,
                                      list<uint64_t> l1, list<uint64_t> l2) {
    std::optional<list<uint64_t>> _root{};
    std::shared_ptr<list<uint64_t>> *_write = nullptr;
    list<uint64_t> _loop_l2 = std::move(l2);
    list<uint64_t> _loop_l1 = std::move(l1);
    uint64_t _loop_fuel = fuel;
    while (true) {
      if (_loop_fuel <= 0) {
        auto _value = std::move(_loop_l1);
        (_write
             ? *(*_write = std::make_shared<list<uint64_t>>(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        uint64_t f = _loop_fuel - 1;
        if (std::holds_alternative<typename list<uint64_t>::Nil>(
                _loop_l1.v_mut())) {
          auto _value = std::move(_loop_l2);
          (_write ? *(*_write =
                          std::make_shared<list<uint64_t>>(std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          auto &[a0, a1] =
              std::get<typename list<uint64_t>::Cons>(_loop_l1.v_mut());
          if (std::holds_alternative<typename list<uint64_t>::Nil>(
                  _loop_l2.v_mut())) {
            auto _value = _loop_l1;
            (_write ? *(*_write =
                            std::make_shared<list<uint64_t>>(std::move(_value)))
                    : _root.emplace(std::move(_value)));
            break;
          } else {
            auto &[a00, a10] =
                std::get<typename list<uint64_t>::Cons>(_loop_l2.v_mut());
            if (cmp(a0, a00) <= UINT64_C(0)) {
              auto _cell = typename list<uint64_t>::Cons(a0, nullptr);
              list<uint64_t> &_node =
                  (_write ? *(*_write = std::make_shared<list<uint64_t>>(
                                  std::move(_cell)))
                          : _root.emplace(std::move(_cell)));
              _write =
                  &std::get<typename list<uint64_t>::Cons>(_node.v_mut()).l;
              _loop_l1 = list<uint64_t>(*a1);
              _loop_fuel = f;
              continue;
            } else {
              auto _cell = typename list<uint64_t>::Cons(a00, nullptr);
              list<uint64_t> &_node =
                  (_write ? *(*_write = std::make_shared<list<uint64_t>>(
                                  std::move(_cell)))
                          : _root.emplace(std::move(_cell)));
              _write =
                  &std::get<typename list<uint64_t>::Cons>(_node.v_mut()).l;
              _loop_l2 = list<uint64_t>(*a10);
              _loop_fuel = f;
              continue;
            }
          }
        }
      }
    }
    return std::move(*_root);
  }

  template <typename F0>
  static list<uint64_t> merge_by(F0 &&cmp, const list<uint64_t> &l1,
                                 const list<uint64_t> &l2) {
    return merge_by_fuel((list_len(l1) + list_len(l2)), cmp, l1, l2);
  }

  /// process_twice l applies recursion twice: process(process(xs)).
  static list<uint64_t> process_twice_fuel(uint64_t fuel, list<uint64_t> l);
  static list<uint64_t> process_twice(const list<uint64_t> &l);
  /// as_guard l uses as-pattern with guard (length check).
  static list<uint64_t> as_guard_fuel(uint64_t fuel, const list<uint64_t> &l);
  static list<uint64_t> as_guard(const list<uint64_t> &l);
  /// quad_sum_pattern l pattern with 4-way split.
  static uint64_t quad_sum_pattern(const list<uint64_t> &l);
  /// multi_guard l demonstrates pattern with multiple conditional branches.
  static uint64_t multi_guard(const list<uint64_t> &l);
  /// Internal helper for double_append.
  static list<uint64_t> append_lists(const list<uint64_t> &l1,
                                     list<uint64_t> l2);
  /// double_append l1 l2 uses recursive result twice: h :: (rest @ rest).
  static list<uint64_t> double_append(const list<uint64_t> &l1,
                                      list<uint64_t> l2);
  /// process_twice_alt l applies transformation twice on recursive result.
  static list<uint64_t> process_twice_alt_fuel(uint64_t fuel, list<uint64_t> l);
  static list<uint64_t> process_twice_alt(const list<uint64_t> &l);
  /// sum_if_positive_else_double l conditional logic on each element.
  static uint64_t sum_if_positive_else_double(const list<uint64_t> &l);

  /// take_until p l takes elements until predicate is true.
  template <typename F0>
  static list<uint64_t> take_until(F0 &&p, const list<uint64_t> &l) {
    std::optional<list<uint64_t>> _root{};
    std::shared_ptr<list<uint64_t>> *_write = nullptr;
    const list<uint64_t> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename list<uint64_t>::Nil>(_loop_l->v())) {
        auto _value = list<uint64_t>::nil();
        (_write
             ? *(*_write = std::make_shared<list<uint64_t>>(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename list<uint64_t>::Cons>(_loop_l->v());
        if (p(a0)) {
          auto _value = list<uint64_t>::nil();
          (_write ? *(*_write =
                          std::make_shared<list<uint64_t>>(std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          auto _cell = typename list<uint64_t>::Cons(a0, nullptr);
          list<uint64_t> &_node =
              (_write ? *(*_write = std::make_shared<list<uint64_t>>(
                              std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write = &std::get<typename list<uint64_t>::Cons>(_node.v_mut()).l;
          _loop_l = crane_raw(a1);
          continue;
        }
      }
    }
    return std::move(*_root);
  }

  /// partition_by p q l partitions into 3 categories based on two predicates.
  template <typename F0, typename F1>
  static std::pair<std::pair<list<uint64_t>, list<uint64_t>>, list<uint64_t>>
  partition_by(
      F0 &&p, F1 &&q,
      const list<uint64_t> &l) { /// CraneEnter: captures varying parameters for
                                 /// each recursive call.

    struct CraneEnter {
      const list<uint64_t> *l;
    };

    /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_Cons {
      uint64_t a0;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    std::pair<std::pair<list<uint64_t>, list<uint64_t>>, list<uint64_t>>
        _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified partition_by: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const list<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename list<uint64_t>::Nil>(l.v())) {
          _result = std::make_pair(
              std::make_pair(list<uint64_t>::nil(), list<uint64_t>::nil()),
              list<uint64_t>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename list<uint64_t>::Cons>(l.v());
          _stack.emplace_back(CraneCont_Cons{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        uint64_t a0 = _f.a0;
        auto [p0, cs] = std::move(_result);
        auto [as_, bs] = std::move(p0);
        if (p(a0)) {
          _result = std::make_pair(
              std::make_pair(list<uint64_t>::cons(a0, std::move(as_)),
                             std::move(bs)),
              std::move(cs));
        } else {
          if (q(a0)) {
            _result = std::make_pair(
                std::make_pair(std::move(as_),
                               list<uint64_t>::cons(a0, std::move(bs))),
                std::move(cs));
          } else {
            _result =
                std::make_pair(std::make_pair(std::move(as_), std::move(bs)),
                               list<uint64_t>::cons(a0, std::move(cs)));
          }
        }
      }
    }
    return _result;
  }

  /// merge_alternating l1 l2 merges two lists by alternating elements.
  static list<uint64_t> merge_alternating(list<uint64_t> l1, list<uint64_t> l2);

  /// filter_map_indexed p f l filters and maps with index.
  template <typename F0, typename F1>
  static list<uint64_t> filter_map_indexed_aux(F0 &&p, F1 &&f,
                                               const list<uint64_t> &l,
                                               uint64_t idx) {
    std::optional<list<uint64_t>> _root{};
    std::shared_ptr<list<uint64_t>> *_write = nullptr;
    uint64_t _loop_idx = idx;
    const list<uint64_t> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename list<uint64_t>::Nil>(_loop_l->v())) {
        auto _value = list<uint64_t>::nil();
        (_write
             ? *(*_write = std::make_shared<list<uint64_t>>(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename list<uint64_t>::Cons>(_loop_l->v());
        if (p(_loop_idx, a0)) {
          auto _cell = typename list<uint64_t>::Cons(f(a0), nullptr);
          list<uint64_t> &_node =
              (_write ? *(*_write = std::make_shared<list<uint64_t>>(
                              std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write = &std::get<typename list<uint64_t>::Cons>(_node.v_mut()).l;
          _loop_idx = (_loop_idx + 1);
          _loop_l = crane_raw(a1);
          continue;
        } else {
          _loop_idx = (_loop_idx + 1);
          _loop_l = crane_raw(a1);
          continue;
        }
      }
    }
    return std::move(*_root);
  }

  template <typename F0, typename F1>
  static list<uint64_t> filter_map_indexed(F0 &&p, F1 &&f,
                                           const list<uint64_t> &l) {
    return filter_map_indexed_aux(p, f, l, UINT64_C(0));
  }

  /// four_elem l four-element destructuring pattern with fallback cases.
  static uint64_t four_elem(const list<uint64_t> &l);
};

#endif // INCLUDED_LOOPIFY_PATTERNS
