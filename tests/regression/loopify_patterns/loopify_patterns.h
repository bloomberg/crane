#ifndef INCLUDED_LOOPIFY_PATTERNS
#define INCLUDED_LOOPIFY_PATTERNS

#include <any>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

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

    template <typename _U> explicit list(const list<_U> &_other) {
      if (std::holds_alternative<typename list<_U>::Nil>(_other.v())) {
        this->v_ = Nil{};
      } else {
        const auto &[a, l] = std::get<typename list<_U>::Cons>(_other.v());
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
                  return A{
                      [&]() -> typename A::first_type {
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
            l ? std::make_shared<list<A>>(*l) : nullptr};
      }
    }

    static list<A> nil() { return list(Nil{}); }

    static list<A> cons(A a, list<A> l) {
      return list(Cons{std::move(a), std::make_shared<list<A>>(std::move(l))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &, list<T1> &, T2 &>
  static T2
  list_rect(T2 f, F1 &&f0,
            const list<T1> &l) { /// _Enter: captures varying parameters for
                                 /// each recursive call.

    struct _Enter {
      const list<T1> *l;
    };

    /// _Resume_Cons: saves [f0, a1, a0], resumes after recursive call with
    /// _result.
    struct _Resume_Cons {
      F1 f0;
      list<T1> a1;
      T1 a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified list_rect: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> &l = *_f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = std::move(f);
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{f0, *a1, a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = _f.f0(_f.a0, _f.a1, _result);
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T1 &, list<T1> &, T2 &>
  static T2
  list_rec(T2 f, F1 &&f0,
           const list<T1> &l) { /// _Enter: captures varying parameters for each
                                /// recursive call.

    struct _Enter {
      const list<T1> *l;
    };

    /// _Resume_Cons: saves [f0, a1, a0], resumes after recursive call with
    /// _result.
    struct _Resume_Cons {
      F1 f0;
      list<T1> a1;
      T1 a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified list_rec: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> &l = *_f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = std::move(f);
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{f0, *a1, a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = _f.f0(_f.a0, _f.a1, _result);
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
  split_by_sign_aux(const list<uint64_t> &l, uint64_t base, list<uint64_t> pos,
                    list<uint64_t> neg);
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
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static uint64_t
  max_by(F0 &&f,
         const list<uint64_t> &l) { /// _Enter: captures varying parameters for
                                    /// each recursive call.

    struct _Enter {
      const list<uint64_t> *l;
    };

    /// _Cont_Cons: saves [a0, f], resumes after recursive call, then processes
    /// rest.
    struct _Cont_Cons {
      uint64_t a0;
      F0 f;
    };

    using _Frame = std::variant<_Enter, _Cont_Cons>;
    uint64_t _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified max_by: _Enter -> _Cont_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename list<uint64_t>::Nil>(l.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename list<uint64_t>::Cons>(l.v());
          auto &&_sv = *a1;
          if (std::holds_alternative<typename list<uint64_t>::Nil>(_sv.v())) {
            _result = f(a0);
          } else {
            _stack.emplace_back(_Cont_Cons{a0, f});
            _stack.emplace_back(_Enter{a1.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Cont_Cons>(_frame));
        uint64_t a0 = _f.a0;
        F0 f = _f.f;
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
  insert_everywhere(T1 x,
                    const list<T1> &l) { /// _Enter: captures varying parameters
                                         /// for each recursive call.

    struct _Enter {
      const list<T1> *l;
    };

    /// _Resume_Cons: saves [_s0, map_cons_h], resumes after recursive call with
    /// _result.
    struct _Resume_Cons {
      std::decay_t<decltype(list<T1>::cons(
          std::declval<T1 &>(),
          list<T1>::cons(std::declval<T1 &>(),
                         *(std::declval<std::shared_ptr<list<T1>> &>()))))>
          _s0;
      std::function<list<list<T1>>(list<list<T1>>)> map_cons_h;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    list<list<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified insert_everywhere: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> &l = *_f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = list<list<T1>>::cons(list<T1>::cons(x, list<T1>::nil()),
                                         list<list<T1>>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
          auto map_cons_h_impl =
              [&](auto &_self_map_cons_h,
                  const list<list<T1>> &lsts) -> list<list<T1>> {
            if (std::holds_alternative<typename list<list<T1>>::Nil>(
                    lsts.v())) {
              return list<list<T1>>::nil();
            } else {
              const auto &[a00, a10] =
                  std::get<typename list<list<T1>>::Cons>(lsts.v());
              return list<list<T1>>::cons(
                  list<T1>::cons(a0, a00),
                  _self_map_cons_h(_self_map_cons_h, *a10));
            }
          };
          auto map_cons_h = [&](const list<list<T1>> &lsts) -> list<list<T1>> {
            return map_cons_h_impl(map_cons_h_impl, lsts);
          };
          _stack.emplace_back(
              _Resume_Cons{list<T1>::cons(x, list<T1>::cons(a0, *a1)),
                           std::move(map_cons_h)});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = list<list<T1>>::cons(_f._s0, _f.map_cons_h(_result));
      }
    }
    return _result;
  }

  /// Helper: list length.
  static uint64_t list_len(const list<uint64_t> &l);

  /// merge_by cmp l1 l2 merge with custom comparator.
  template <typename F1>
    requires std::is_invocable_r_v<uint64_t, F1 &, uint64_t &, uint64_t &>
  static list<uint64_t>
  merge_by_fuel(uint64_t fuel, F1 &&cmp, list<uint64_t> l1,
                list<uint64_t> l2) { /// _Enter: captures varying parameters for
                                     /// each recursive call.

    struct _Enter {
      list<uint64_t> l2;
      list<uint64_t> l1;
      uint64_t fuel;
    };

    /// _Resume1: saves [a0], resumes after recursive call with _result.
    struct _Resume1 {
      uint64_t a0;
    };

    /// _Resume2: saves [a00], resumes after recursive call with _result.
    struct _Resume2 {
      uint64_t a00;
    };

    using _Frame = std::variant<_Enter, _Resume1, _Resume2>;
    list<uint64_t> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{std::move(l2), std::move(l1), fuel});
    /// Loopified merge_by_fuel: _Enter -> _Resume1 -> _Resume2.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        list<uint64_t> l2 = std::move(_f.l2);
        list<uint64_t> l1 = std::move(_f.l1);
        uint64_t fuel = _f.fuel;
        if (fuel <= 0) {
          _result = std::move(l1);
        } else {
          uint64_t f = fuel - 1;
          if (std::holds_alternative<typename list<uint64_t>::Nil>(
                  l1.v_mut())) {
            _result = std::move(l2);
          } else {
            auto &[a0, a1] =
                std::get<typename list<uint64_t>::Cons>(l1.v_mut());
            if (std::holds_alternative<typename list<uint64_t>::Nil>(
                    l2.v_mut())) {
              _result = std::move(l1);
            } else {
              auto &[a00, a10] =
                  std::get<typename list<uint64_t>::Cons>(l2.v_mut());
              if (cmp(a0, a00) <= UINT64_C(0)) {
                _stack.emplace_back(_Resume1{std::move(a0)});
                _stack.emplace_back(_Enter{l2, *a1, f});
              } else {
                _stack.emplace_back(_Resume2{std::move(a00)});
                _stack.emplace_back(_Enter{*a10, l1, f});
              }
            }
          }
        }
      } else if (std::holds_alternative<_Resume1>(_frame)) {
        auto _f = std::move(std::get<_Resume1>(_frame));
        _result = list<uint64_t>::cons(_f.a0, _result);
      } else {
        auto _f = std::move(std::get<_Resume2>(_frame));
        _result = list<uint64_t>::cons(_f.a00, _result);
      }
    }
    return _result;
  }

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &, uint64_t &>
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
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static list<uint64_t>
  take_until(F0 &&p,
             const list<uint64_t> &l) { /// _Enter: captures varying parameters
                                        /// for each recursive call.

    struct _Enter {
      const list<uint64_t> *l;
    };

    /// _Resume1: saves [a0], resumes after recursive call with _result.
    struct _Resume1 {
      uint64_t a0;
    };

    using _Frame = std::variant<_Enter, _Resume1>;
    list<uint64_t> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified take_until: _Enter -> _Resume1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename list<uint64_t>::Nil>(l.v())) {
          _result = list<uint64_t>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename list<uint64_t>::Cons>(l.v());
          if (p(a0)) {
            _result = list<uint64_t>::nil();
          } else {
            _stack.emplace_back(_Resume1{a0});
            _stack.emplace_back(_Enter{a1.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume1>(_frame));
        _result = list<uint64_t>::cons(_f.a0, _result);
      }
    }
    return _result;
  }

  /// partition_by p q l partitions into 3 categories based on two predicates.
  template <typename F0, typename F1>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &> &&
             std::is_invocable_r_v<bool, F1 &, uint64_t &>
  static std::pair<std::pair<list<uint64_t>, list<uint64_t>>, list<uint64_t>>
  partition_by(
      F0 &&p, F1 &&q,
      const list<uint64_t>
          &l) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      const list<uint64_t> *l;
    };

    /// _Cont_Cons: saves [a0, p, q], resumes after recursive call, then
    /// processes rest.
    struct _Cont_Cons {
      uint64_t a0;
      F0 p;
      F1 q;
    };

    using _Frame = std::variant<_Enter, _Cont_Cons>;
    std::pair<std::pair<list<uint64_t>, list<uint64_t>>, list<uint64_t>>
        _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified partition_by: _Enter -> _Cont_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename list<uint64_t>::Nil>(l.v())) {
          _result = std::make_pair(
              std::make_pair(list<uint64_t>::nil(), list<uint64_t>::nil()),
              list<uint64_t>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename list<uint64_t>::Cons>(l.v());
          _stack.emplace_back(_Cont_Cons{a0, p, q});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Cont_Cons>(_frame));
        uint64_t a0 = _f.a0;
        F0 p = _f.p;
        F1 q = _f.q;
        auto _cs = std::move(_result);
        const std::pair<list<uint64_t>, list<uint64_t>> &p0 = _cs.first;
        const list<uint64_t> &cs = _cs.second;
        const list<uint64_t> &as_ = p0.first;
        const list<uint64_t> &bs = p0.second;
        if (p(a0)) {
          _result = std::make_pair(
              std::make_pair(list<uint64_t>::cons(a0, as_), bs), cs);
        } else {
          if (q(a0)) {
            _result = std::make_pair(
                std::make_pair(as_, list<uint64_t>::cons(a0, bs)), cs);
          } else {
            _result = std::make_pair(std::make_pair(as_, bs),
                                     list<uint64_t>::cons(a0, cs));
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
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &, uint64_t &> &&
             std::is_invocable_r_v<uint64_t, F1 &, uint64_t &>
  static list<uint64_t>
  filter_map_indexed_aux(F0 &&p, F1 &&f, const list<uint64_t> &l,
                         uint64_t idx) { /// _Enter: captures varying parameters
                                         /// for each recursive call.

    struct _Enter {
      uint64_t idx;
      const list<uint64_t> *l;
    };

    /// _Resume1: saves [a0], resumes after recursive call with _result.
    struct _Resume1 {
      uint64_t a0;
    };

    using _Frame = std::variant<_Enter, _Resume1>;
    list<uint64_t> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{idx, &l});
    /// Loopified filter_map_indexed_aux: _Enter -> _Resume1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        uint64_t idx = _f.idx;
        const list<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename list<uint64_t>::Nil>(l.v())) {
          _result = list<uint64_t>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename list<uint64_t>::Cons>(l.v());
          if (p(idx, a0)) {
            _stack.emplace_back(_Resume1{f(a0)});
            _stack.emplace_back(_Enter{(idx + 1), a1.get()});
          } else {
            _stack.emplace_back(_Enter{(idx + 1), a1.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume1>(_frame));
        _result = list<uint64_t>::cons(_f.a0, _result);
      }
    }
    return _result;
  }

  template <typename F0, typename F1>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &, uint64_t &> &&
             std::is_invocable_r_v<uint64_t, F1 &, uint64_t &>
  static list<uint64_t> filter_map_indexed(F0 &&p, F1 &&f,
                                           const list<uint64_t> &l) {
    return filter_map_indexed_aux(p, f, l, UINT64_C(0));
  }

  /// four_elem l four-element destructuring pattern with fallback cases.
  static uint64_t four_elem(const list<uint64_t> &l);
};

#endif // INCLUDED_LOOPIFY_PATTERNS
