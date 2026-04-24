#ifndef INCLUDED_LOOPIFY_PATTERNS
#define INCLUDED_LOOPIFY_PATTERNS

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> struct is_shared_ptr : std::false_type {};

template <typename T>
struct is_shared_ptr<std::shared_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  return x ? std::make_unique<T>(x->clone()) : nullptr;
}

template <typename T>
std::shared_ptr<T> clone_value(const std::shared_ptr<T> &x) {
  return x ? std::make_shared<T>(x->clone()) : nullptr;
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using TargetBare = std::remove_cvref_t<Target>;
  using SourceBare = std::remove_cvref_t<Source>;
  if constexpr (is_unique_ptr<TargetBare>::value) {
    using Inner = typename is_unique_ptr<TargetBare>::element_type;
    if constexpr (is_unique_ptr<SourceBare>::value) {
      using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires {
                             typename Inner::crane_element_type;
                             x->template clone_as<
                                 typename Inner::crane_element_type>();
                           }) {
        return std::make_unique<Inner>(
            x->template clone_as<typename Inner::crane_element_type>());
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_unique<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x.clone());
      }
    }
  } else if constexpr (is_shared_ptr<TargetBare>::value) {
    using Inner = typename is_shared_ptr<TargetBare>::element_type;
    if constexpr (is_shared_ptr<SourceBare>::value) {
      using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else if constexpr (is_unique_ptr<SourceBare>::value) {
      if (!x)
        return nullptr;
      if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_shared<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x.clone());
      }
    }
  } else if constexpr (std::is_same_v<TargetBare, SourceBare>) {
    return clone_value(x);
  } else if constexpr (is_unique_ptr<SourceBare>::value) {
    using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (is_shared_ptr<SourceBare>::value) {
    using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (requires {
                         typename TargetBare::crane_element_type;
                         x.template clone_as<
                             typename TargetBare::crane_element_type>();
                       }) {
    return x.template clone_as<typename TargetBare::crane_element_type>();
  } else if constexpr (requires { x.template clone_as<TargetBare>(); }) {
    return x.template clone_as<TargetBare>();
  } else {
    return Target(x);
  }
}

/// Complex control flow and pattern matching edge cases.
struct LoopifyPatterns {
  template <typename t_A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      t_A d_a0;
      std::unique_ptr<list<t_A>> d_a1;
    };

    using variant_t = std::variant<Nil, Cons>;
    using crane_element_type = t_A;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    list() {}

    explicit list(Nil _v) : d_v_(_v) {}

    explicit list(Cons _v) : d_v_(std::move(_v)) {}

    list(const list<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    list(list<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) list<t_A> &operator=(const list<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) list<t_A> &operator=(list<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) list<t_A> clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Nil>(_sv.v())) {
        return list<t_A>(Nil{});
      } else {
        const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
        return list<t_A>(
            Cons{clone_as_value<t_A>(d_a0),
                 clone_as_value<std::unique_ptr<list<t_A>>>(d_a1)});
      }
    }

    template <typename _CloneT0>
    __attribute__((pure)) list<_CloneT0> clone_as() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Nil>(_sv.v())) {
        return list<_CloneT0>(typename list<_CloneT0>::Nil{});
      } else {
        const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
        return list<_CloneT0>(typename list<_CloneT0>::Cons{
            clone_as_value<_CloneT0>(d_a0),
            clone_as_value<std::unique_ptr<list<_CloneT0>>>(d_a1)});
      }
    }

    // CREATORS
    __attribute__((pure)) static list<t_A> nil() { return list(Nil{}); }

    __attribute__((pure)) static list<t_A> cons(t_A a0, const list<t_A> &a1) {
      return list(Cons{std::move(a0), std::make_unique<list<t_A>>(a1.clone())});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) list<t_A> *operator->() { return this; }

    __attribute__((pure)) const list<t_A> *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = list<t_A>(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, MapsTo<T2, T1, list<T1>, T2> F1>
  static T2 list_rect(const T2 f, F1 &&f0, const list<T1> &l) {
    struct _Enter {
      const list<T1> l;
    };

    struct _Call1 {
      list<T1> _s0;
      T1 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> l = _f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = f;
        } else {
          const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v());
          _stack.emplace_back(_Call1{*(d_a1), d_a0});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = f0(_f._s1, _f._s0, _result);
      }
    }
    return _result;
  }

  template <typename T1, typename T2, MapsTo<T2, T1, list<T1>, T2> F1>
  static T2 list_rec(const T2 f, F1 &&f0, const list<T1> &l) {
    struct _Enter {
      const list<T1> l;
    };

    struct _Call1 {
      list<T1> _s0;
      T1 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> l = _f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = f;
        } else {
          const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v());
          _stack.emplace_back(_Call1{*(d_a1), d_a0});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = f0(_f._s1, _f._s0, _result);
      }
    }
    return _result;
  }

  /// multi_let n multiple sequential let bindings before recursion.
  __attribute__((pure)) static unsigned int multi_let(const unsigned int &n);
  /// nested_if n deeply nested if-then-else with recursion at different depths.
  __attribute__((pure)) static unsigned int
  nested_if_fuel(const unsigned int &fuel, const unsigned int &n);
  __attribute__((pure)) static unsigned int nested_if(const unsigned int &n);
  /// deep_nest n deeply nested function application.
  __attribute__((pure)) static unsigned int deep_nest(const unsigned int &n);
  /// bool_chain n target multiple recursive calls in || chain.
  __attribute__((pure)) static bool bool_chain_fuel(const unsigned int &fuel,
                                                    const unsigned int &n,
                                                    const unsigned int &target);
  __attribute__((pure)) static bool bool_chain(const unsigned int &n,
                                               const unsigned int &target);
  /// chained_comp n boolean result with double recursion.
  __attribute__((pure)) static bool chained_comp(const unsigned int &n);
  /// tuple_constr n recursive calls in multiple tuple positions.
  __attribute__((pure)) static std::pair<std::pair<unsigned int, unsigned int>,
                                         unsigned int>
  tuple_constr(const unsigned int &n);
  /// sum_prod_count l a_sum a_prod a_count multiple accumulator updates.
  __attribute__((pure)) static std::pair<std::pair<unsigned int, unsigned int>,
                                         unsigned int>
  sum_prod_count(const list<unsigned int> &l, unsigned int a_sum,
                 unsigned int a_prod, unsigned int a_count);
  /// split_by_sign l pos neg partition with dual accumulators.
  __attribute__((pure)) static std::pair<list<unsigned int>, list<unsigned int>>
  split_by_sign_aux(const list<unsigned int> &l, const unsigned int &base,
                    list<unsigned int> pos, list<unsigned int> neg);
  __attribute__((pure)) static std::pair<list<unsigned int>, list<unsigned int>>
  split_by_sign(const list<unsigned int> &l, const unsigned int &base);
  /// guard_accum acc l multiple when-style guards with different logic.
  __attribute__((pure)) static unsigned int
  guard_accum(unsigned int acc, const list<unsigned int> &l);
  /// cons_computed n l cons with conditional parameter change.
  __attribute__((pure)) static list<unsigned int>
  cons_computed(const unsigned int &n, const list<unsigned int> &l);
  /// mod_pattern n recursive call in mod expression.
  __attribute__((pure)) static unsigned int mod_pattern(const unsigned int &n);
  /// alternating_ops n alternating operations based on modulo.
  __attribute__((pure)) static unsigned int
  alternating_ops(const unsigned int &n);

  /// max_by f l recursive max with function application.
  template <MapsTo<unsigned int, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  max_by(F0 &&f, const list<unsigned int> &l) {
    struct _Enter {
      const list<unsigned int> l;
    };

    struct _Call1 {
      unsigned int _s0;
      F0 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<unsigned int> l = _f.l;
        if (std::holds_alternative<typename list<unsigned int>::Nil>(l.v())) {
          _result = 0u;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename list<unsigned int>::Cons>(l.v());
          auto &&_sv = *(d_a1);
          if (std::holds_alternative<typename list<unsigned int>::Nil>(
                  _sv.v())) {
            _result = f(d_a0);
          } else {
            _stack.emplace_back(_Call1{d_a0, f});
            _stack.emplace_back(_Enter{*(d_a1)});
          }
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        unsigned int d_a0 = _f._s0;
        F0 f = _f._s1;
        unsigned int rest_max = _result;
        unsigned int fx = f(d_a0);
        if (fx < rest_max) {
          _result = rest_max;
        } else {
          _result = fx;
        }
      }
    }
    return _result;
  }

  /// replace_at idx value l replace element at index.
  __attribute__((pure)) static list<unsigned int>
  replace_at(const unsigned int &idx, unsigned int value,
             const list<unsigned int> &l);
  /// nested_pattern l three-element tuple pattern.
  __attribute__((pure)) static unsigned int nested_pattern(
      const list<std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>
          &l);
  /// let_nested n let with nested let in binding.
  __attribute__((pure)) static unsigned int let_nested(const unsigned int &n);

  /// insert_everywhere x l insert element at all possible positions.
  template <typename T1>
  __attribute__((pure)) static list<list<T1>>
  insert_everywhere(const T1 x, const list<T1> &l) {
    struct _Enter {
      const list<T1> l;
    };

    struct _Call1 {
      decltype(list<T1>::cons(std::declval<const T1 &>(),
                              list<T1>::cons(std::declval<T1 &>(),
                                             std::declval<list<T1> &>()))) _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    list<list<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<T1> l = _f.l;
        if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
          _result = list<list<T1>>::cons(list<T1>::cons(x, list<T1>::nil()),
                                         list<list<T1>>::nil());
        } else {
          const auto &[d_a0, d_a1] = std::get<typename list<T1>::Cons>(l.v());
          list<T1> d_a1_value = clone_as_value<list<T1>>(d_a1);
          std::function<list<list<T1>>(list<list<T1>>)> map_cons_h;
          map_cons_h = [&](list<list<T1>> lsts) -> list<list<T1>> {
            struct _Enter {
              list<list<T1>> lsts;
            };
            struct _Call1 {
              decltype(list<T1>::cons(
                  d_a0, clone_as_value<list<T1>>(
                            std::declval<std::unique_ptr<list<T1>> &>()))) _s0;
            };
            using _Frame = std::variant<_Enter, _Call1>;
            list<list<T1>> _result{};
            std::vector<_Frame> _stack;
            _stack.reserve(16);
            _stack.emplace_back(_Enter{lsts});
            while (!_stack.empty()) {
              _Frame _frame = std::move(_stack.back());
              _stack.pop_back();
              if (std::holds_alternative<_Enter>(_frame)) {
                auto _f = std::move(std::get<_Enter>(_frame));
                list<list<T1>> lsts = _f.lsts;
                if (std::holds_alternative<typename list<list<T1>>::Nil>(
                        lsts.v())) {
                  _result = list<list<T1>>::nil();
                } else {
                  const auto &[d_a00, d_a10] =
                      std::get<typename list<list<T1>>::Cons>(lsts.v());
                  _stack.emplace_back(_Call1{
                      list<T1>::cons(d_a0, clone_as_value<list<T1>>(d_a00))});
                  _stack.emplace_back(_Enter{*(d_a10)});
                }
              } else {
                auto _f = std::move(std::get<_Call1>(_frame));
                _result = list<list<T1>>::cons(_f._s0, _result);
              }
            }
            return _result;
          };
          _stack.emplace_back(
              _Call1{list<T1>::cons(x, list<T1>::cons(d_a0, d_a1_value))});
          _stack.emplace_back(_Enter{d_a1_value});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = list<list<T1>>::cons(_f._s0, map_cons_h(_result));
      }
    }
    return _result;
  }

  /// Helper: list length.
  __attribute__((pure)) static unsigned int
  list_len(const list<unsigned int> &l);

  /// merge_by cmp l1 l2 merge with custom comparator.
  template <MapsTo<unsigned int, unsigned int, unsigned int> F1>
  __attribute__((pure)) static list<unsigned int>
  merge_by_fuel(const unsigned int &fuel, F1 &&cmp, list<unsigned int> l1,
                list<unsigned int> l2) {
    std::unique_ptr<list<unsigned int>> _head{};
    std::unique_ptr<list<unsigned int>> *_write = &_head;
    list<unsigned int> _loop_l2 = std::move(l2);
    list<unsigned int> _loop_l1 = std::move(l1);
    unsigned int _loop_fuel = fuel;
    while (true) {
      if (_loop_fuel <= 0) {
        *(_write) = std::make_unique<list<unsigned int>>(_loop_l1);
        break;
      } else {
        unsigned int f = _loop_fuel - 1;
        if (std::holds_alternative<typename list<unsigned int>::Nil>(
                _loop_l1.v())) {
          *(_write) = std::make_unique<list<unsigned int>>(_loop_l2);
          break;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename list<unsigned int>::Cons>(_loop_l1.v());
          if (std::holds_alternative<typename list<unsigned int>::Nil>(
                  _loop_l2.v())) {
            *(_write) = std::make_unique<list<unsigned int>>(_loop_l1);
            break;
          } else {
            const auto &[d_a00, d_a10] =
                std::get<typename list<unsigned int>::Cons>(_loop_l2.v());
            if (cmp(d_a0, d_a00) <= 0u) {
              auto _cell = std::make_unique<list<unsigned int>>(
                  typename list<unsigned int>::Cons(d_a0, nullptr));
              *(_write) = std::move(_cell);
              _write = &std::get<typename list<unsigned int>::Cons>(
                            (*_write)->v_mut())
                            .d_a1;
              list<unsigned int> _next_l1 = *(d_a1);
              unsigned int _next_fuel = f;
              _loop_l1 = std::move(_next_l1);
              _loop_fuel = std::move(_next_fuel);
              continue;
            } else {
              auto _cell = std::make_unique<list<unsigned int>>(
                  typename list<unsigned int>::Cons(d_a00, nullptr));
              *(_write) = std::move(_cell);
              _write = &std::get<typename list<unsigned int>::Cons>(
                            (*_write)->v_mut())
                            .d_a1;
              list<unsigned int> _next_l2 = *(d_a10);
              unsigned int _next_fuel = f;
              _loop_l2 = std::move(_next_l2);
              _loop_fuel = std::move(_next_fuel);
              continue;
            }
          }
        }
      }
    }
    return std::move(*(_head));
  }

  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  __attribute__((pure)) static list<unsigned int>
  merge_by(F0 &&cmp, const list<unsigned int> &l1,
           const list<unsigned int> &l2) {
    return merge_by_fuel((list_len(l1) + list_len(l2)), cmp, l1, l2);
  }

  /// process_twice l applies recursion twice: process(process(xs)).
  __attribute__((pure)) static list<unsigned int>
  process_twice_fuel(const unsigned int &fuel, list<unsigned int> l);
  __attribute__((pure)) static list<unsigned int>
  process_twice(const list<unsigned int> &l);
  /// as_guard l uses as-pattern with guard (length check).
  __attribute__((pure)) static list<unsigned int>
  as_guard_fuel(const unsigned int &fuel, const list<unsigned int> &l);
  __attribute__((pure)) static list<unsigned int>
  as_guard(const list<unsigned int> &l);
  /// quad_sum_pattern l pattern with 4-way split.
  __attribute__((pure)) static unsigned int
  quad_sum_pattern(const list<unsigned int> &l);
  /// multi_guard l demonstrates pattern with multiple conditional branches.
  __attribute__((pure)) static unsigned int
  multi_guard(const list<unsigned int> &l);
  /// Internal helper for double_append.
  __attribute__((pure)) static list<unsigned int>
  append_lists(const list<unsigned int> &l1, list<unsigned int> l2);
  /// double_append l1 l2 uses recursive result twice: h :: (rest @ rest).
  __attribute__((pure)) static list<unsigned int>
  double_append(const list<unsigned int> &l1, list<unsigned int> l2);
  /// process_twice_alt l applies transformation twice on recursive result.
  __attribute__((pure)) static list<unsigned int>
  process_twice_alt_fuel(const unsigned int &fuel, list<unsigned int> l);
  __attribute__((pure)) static list<unsigned int>
  process_twice_alt(const list<unsigned int> &l);
  /// sum_if_positive_else_double l conditional logic on each element.
  __attribute__((pure)) static unsigned int
  sum_if_positive_else_double(const list<unsigned int> &l);

  /// take_until p l takes elements until predicate is true.
  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static list<unsigned int>
  take_until(F0 &&p, const list<unsigned int> &l) {
    std::unique_ptr<list<unsigned int>> _head{};
    std::unique_ptr<list<unsigned int>> *_write = &_head;
    list<unsigned int> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename list<unsigned int>::Nil>(
              _loop_l.v())) {
        *(_write) =
            std::make_unique<list<unsigned int>>(list<unsigned int>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<unsigned int>::Cons>(_loop_l.v());
        if (p(d_a0)) {
          *(_write) =
              std::make_unique<list<unsigned int>>(list<unsigned int>::nil());
          break;
        } else {
          auto _cell = std::make_unique<list<unsigned int>>(
              typename list<unsigned int>::Cons(d_a0, nullptr));
          *(_write) = std::move(_cell);
          _write =
              &std::get<typename list<unsigned int>::Cons>((*_write)->v_mut())
                   .d_a1;
          _loop_l = *(d_a1);
          continue;
        }
      }
    }
    return std::move(*(_head));
  }

  /// partition_by p q l partitions into 3 categories based on two predicates.
  template <MapsTo<bool, unsigned int> F0, MapsTo<bool, unsigned int> F1>
  __attribute__((pure)) static std::pair<
      std::pair<list<unsigned int>, list<unsigned int>>, list<unsigned int>>
  partition_by(F0 &&p, F1 &&q, const list<unsigned int> &l) {
    struct _Enter {
      const list<unsigned int> l;
    };

    struct _Call1 {
      unsigned int _s0;
      F0 _s1;
      F1 _s2;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<std::pair<list<unsigned int>, list<unsigned int>>,
              list<unsigned int>>
        _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const list<unsigned int> l = _f.l;
        if (std::holds_alternative<typename list<unsigned int>::Nil>(l.v())) {
          _result = std::make_pair(std::make_pair(list<unsigned int>::nil(),
                                                  list<unsigned int>::nil()),
                                   list<unsigned int>::nil());
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename list<unsigned int>::Cons>(l.v());
          _stack.emplace_back(_Call1{d_a0, p, q});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        unsigned int d_a0 = _f._s0;
        F0 p = _f._s1;
        F1 q = _f._s2;
        const std::pair<list<unsigned int>, list<unsigned int>> &p0 =
            _result.first;
        const list<unsigned int> &cs = _result.second;
        const list<unsigned int> &as_ = p0.first;
        const list<unsigned int> &bs = p0.second;
        if (p(d_a0)) {
          _result = std::make_pair(
              std::make_pair(list<unsigned int>::cons(d_a0, as_), bs), cs);
        } else {
          if (q(d_a0)) {
            _result = std::make_pair(
                std::make_pair(as_, list<unsigned int>::cons(d_a0, bs)), cs);
          } else {
            _result = std::make_pair(std::make_pair(as_, bs),
                                     list<unsigned int>::cons(d_a0, cs));
          }
        }
      }
    }
    return _result;
  }

  /// merge_alternating l1 l2 merges two lists by alternating elements.
  __attribute__((pure)) static list<unsigned int>
  merge_alternating(list<unsigned int> l1, list<unsigned int> l2);

  /// filter_map_indexed p f l filters and maps with index.
  template <MapsTo<bool, unsigned int, unsigned int> F0,
            MapsTo<unsigned int, unsigned int> F1>
  __attribute__((pure)) static list<unsigned int>
  filter_map_indexed_aux(F0 &&p, F1 &&f, const list<unsigned int> &l,
                         unsigned int idx) {
    std::unique_ptr<list<unsigned int>> _head{};
    std::unique_ptr<list<unsigned int>> *_write = &_head;
    unsigned int _loop_idx = std::move(idx);
    list<unsigned int> _loop_l = l;
    while (true) {
      if (std::holds_alternative<typename list<unsigned int>::Nil>(
              _loop_l.v())) {
        *(_write) =
            std::make_unique<list<unsigned int>>(list<unsigned int>::nil());
        break;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename list<unsigned int>::Cons>(_loop_l.v());
        if (p(_loop_idx, d_a0)) {
          auto _cell = std::make_unique<list<unsigned int>>(
              typename list<unsigned int>::Cons(f(d_a0), nullptr));
          *(_write) = std::move(_cell);
          _write =
              &std::get<typename list<unsigned int>::Cons>((*_write)->v_mut())
                   .d_a1;
          unsigned int _next_idx = (_loop_idx + 1);
          list<unsigned int> _next_l = *(d_a1);
          _loop_idx = std::move(_next_idx);
          _loop_l = std::move(_next_l);
          continue;
        } else {
          unsigned int _next_idx = (_loop_idx + 1);
          list<unsigned int> _next_l = *(d_a1);
          _loop_idx = std::move(_next_idx);
          _loop_l = std::move(_next_l);
          continue;
        }
      }
    }
    return std::move(*(_head));
  }

  template <MapsTo<bool, unsigned int, unsigned int> F0,
            MapsTo<unsigned int, unsigned int> F1>
  __attribute__((pure)) static list<unsigned int>
  filter_map_indexed(F0 &&p, F1 &&f, const list<unsigned int> &l) {
    return filter_map_indexed_aux(p, f, l, 0u);
  }

  /// four_elem l four-element destructuring pattern with fallback cases.
  __attribute__((pure)) static unsigned int
  four_elem(const list<unsigned int> &l);
};

#endif // INCLUDED_LOOPIFY_PATTERNS
