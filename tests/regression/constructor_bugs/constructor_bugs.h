#ifndef INCLUDED_CONSTRUCTOR_BUGS
#define INCLUDED_CONSTRUCTOR_BUGS

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;
template <typename A> struct Sig;

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
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

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
};

template <typename A> struct Sig {
  // DATA
  A x;

  // ACCESSORS
  Sig<A> clone() const { return {x}; }

  template <typename CraneU> operator Sig<CraneU>() const {
    return {[&]() -> CraneU {
      if constexpr (crane_convertible<CraneU, const A &>) {
        return crane_convert<CraneU>(x);
      } else {
        throw std::logic_error(
            "unreachable: inactive constructor field at this instantiation");
      }
    }()};
  }

  // CREATORS
  static Sig<A> exist(A x) { return {std::move(x)}; }
};

struct ConstructorBugs {
  struct field_a {
    uint64_t a_value;
  };

  struct field_b {
    uint64_t b_value;
  };

  struct source_state {
    field_a source_a;
    field_b source_b;
    uint64_t source_flag;
  };

  struct packed_state {
    source_state packed_source;
    field_a packed_a;
    field_b packed_b;
  };

  static source_state step(source_state s);
  static std::pair<bool, packed_state> bad_branch(const source_state &s1);
  static std::pair<bool, packed_state> bad_direct(const source_state &s1);
  static source_state step2(const source_state &s);
  static std::pair<bool, packed_state> bad_complex_step(const source_state &s1);
  static std::pair<bool, packed_state> bad_nested(const source_state &s1);

  struct source_state_list {
    field_a source_a_list;
    List<field_b> source_b_list;
    uint64_t source_flag_list;
  };

  struct packed_state_list {
    source_state_list packed_source_list;
    field_a packed_a_list;
    List<field_b> packed_b_list;
  };

  static source_state_list step_list(source_state_list s);
  static std::pair<bool, packed_state_list>
  bad_branch_list(const source_state_list &s1);

  struct state {
    uint64_t value;
    List<uint64_t> data;
  };

  static state get_state(uint64_t n);
  static std::pair<std::pair<state, state>, uint64_t>
  tuple_from_call(uint64_t n);
  static std::pair<std::pair<state, uint64_t>,
                   std::pair<uint64_t, List<uint64_t>>>
  nested_tuples(const state &s);
  static std::pair<std::pair<state, uint64_t>, List<uint64_t>>
  conditional_tuple(bool b, uint64_t n);
  static uint64_t extract_value(const state &s);
  static List<uint64_t> extract_data(const state &s);
  static std::pair<std::pair<state, uint64_t>, List<uint64_t>>
  multi_call_tuple(uint64_t n);
  static std::pair<uint64_t, std::pair<state, uint64_t>> pair_test(uint64_t n);
  static std::optional<std::pair<state, uint64_t>>
  match_test(const std::optional<state> &o);
  static List<state> list_test(const state &s);
  static std::pair<std::pair<std::pair<state, uint64_t>,
                             std::pair<uint64_t, List<uint64_t>>>,
                   List<uint64_t>>
  triple_proj(const state &s);
  static std::pair<state, uint64_t> inner_pair(const state &s);
  static std::pair<state, uint64_t> outer_call(uint64_t n);
  static std::pair<
      std::pair<std::pair<std::pair<state, state>, uint64_t>, uint64_t>,
      List<uint64_t>>
  extreme_reuse(const state &s);

  struct Inner {
    uint64_t inner_val;
  };

  struct Outer {
    Inner outer_inner;
    uint64_t outer_data;
  };

  static Outer nested_record(const Inner &i);
  static Outer self_referential(const Outer &o);
  static std::pair<Inner, uint64_t> pair_with_proj(const Inner &i);
  static std::pair<std::pair<Inner, uint64_t>, std::pair<uint64_t, uint64_t>>
  nested_pairs(const Inner &i);
  static std::pair<Inner, Inner> pair_duplicate(const Inner &i);
  static Inner mk_inner(uint64_t n);
  static std::pair<Inner, uint64_t> pair_from_func(uint64_t n);
  static std::optional<std::pair<Inner, uint64_t>>
  match_option_record(const std::optional<Inner> &o);

  struct MySum {
    // TYPES
    struct Left {
      Inner a0;
    };

    struct Right {
      uint64_t a0;
    };

    using variant_t = std::variant<Left, Right>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    MySum() {}

    explicit MySum(Left _v) : v_(std::move(_v)) {}

    explicit MySum(Right _v) : v_(std::move(_v)) {}

    static MySum left(Inner a0) { return MySum(Left{std::move(a0)}); }

    static MySum right(uint64_t a0) { return MySum(Right{a0}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, Inner &> &&
             std::is_invocable_r_v<T1, F1 &, uint64_t &>
  static T1 MySum_rect(F0 &&f, F1 &&f0, const MySum &m) {
    if (std::holds_alternative<typename MySum::Left>(m.v())) {
      const auto &[a0] = std::get<typename MySum::Left>(m.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename MySum::Right>(m.v());
      return f0(a0);
    }
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, Inner &> &&
             std::is_invocable_r_v<T1, F1 &, uint64_t &>
  static T1 MySum_rec(F0 &&f, F1 &&f0, const MySum &m) {
    if (std::holds_alternative<typename MySum::Left>(m.v())) {
      const auto &[a0] = std::get<typename MySum::Left>(m.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename MySum::Right>(m.v());
      return f0(a0);
    }
  }

  static std::pair<Inner, uint64_t> match_sum(const MySum &s);
  static std::pair<Inner, uint64_t> with_cast(const Inner &i);
  static std::pair<std::pair<Inner, uint64_t>, std::pair<Inner, uint64_t>>
  chain_lets(const Inner &i1);

  struct Container {
    Outer cont_outer;
  };

  static std::pair<std::pair<Outer, Inner>, uint64_t>
  deep_proj(const Container &c);
  static std::pair<List<Inner>, uint64_t> list_with_proj(const Inner &i);
  static std::pair<Inner, uint64_t> tail_pair(const Inner &i, bool b);
  static std::pair<std::pair<Inner, Inner>, std::pair<uint64_t, uint64_t>>
  quad_tuple(const Inner &i);
  static std::pair<std::optional<Inner>, uint64_t>
  match_both_branches(const std::optional<Inner> &o);
  static Sig<Inner> sigma_test(const Inner &i);
  static uint64_t extract(const Inner &i);
  static std::pair<Inner, uint64_t> nested_extract(const Inner &i);
  static std::pair<Outer, uint64_t> update_test(const Outer &o);

  struct State0 {
    uint64_t value_inline;
    uint64_t data_inline;
    uint64_t flag;
  };

  static std::pair<State0, uint64_t> inline_pair(const State0 &s);
  static std::pair<std::pair<State0, uint64_t>, uint64_t>
  inline_triple(const State0 &s);
  static std::pair<std::pair<State0, uint64_t>, uint64_t>
  inline_nested(const State0 &s);
  static State0 get_state_inline(uint64_t n);
  static std::pair<State0, uint64_t> inline_from_call(uint64_t n);
  static std::pair<std::pair<State0, uint64_t>, uint64_t>
  same_call_multi_proj(uint64_t n);
  static std::optional<std::pair<State0, uint64_t>>
  inline_match(const std::optional<State0> &o);
  static std::pair<State0, uint64_t> inline_if(bool b, const State0 &s);

  struct OuterInline {
    State0 outer_state;
    uint64_t outer_num;
  };

  static std::pair<std::pair<OuterInline, State0>, uint64_t>
  inline_deep(const OuterInline &o);
  static std::pair<State0, uint64_t> inline_double_proj(const OuterInline &o);
  static std::pair<std::pair<State0, uint64_t>, std::pair<uint64_t, uint64_t>>
  inline_many(const State0 &s);
  static std::pair<std::pair<uint64_t, State0>, uint64_t>
  inline_pattern(const State0 &s);
  static List<std::pair<State0, uint64_t>> inline_recursive(uint64_t n,
                                                            const State0 &s);
  static std::pair<std::pair<std::pair<State0, uint64_t>, uint64_t>,
                   std::pair<uint64_t, State0>>
  inline_complex(const State0 &s);
  static std::pair<std::pair<State0, State0>, std::pair<uint64_t, uint64_t>>
  inline_quad(const State0 &s);
  static std::pair<State0, uint64_t> inline_both_branches(bool b,
                                                          const State0 &s);

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, State0 &>
  static std::pair<std::pair<State0, uint64_t>, uint64_t>
  apply_twice(F0 &&f, const State0 &s) {
    return std::make_pair(std::make_pair(s, f(s)), f(s));
  }

  static std::pair<std::pair<State0, uint64_t>, uint64_t>
  test_apply(const State0 &s);
  static uint64_t get_value_inline(const State0 &s);
  static uint64_t get_data_inline(const State0 &s);
  static std::pair<std::pair<State0, uint64_t>, uint64_t>
  inline_nested_calls(const State0 &s);
  static std::pair<std::optional<State0>, std::optional<uint64_t>>
  inline_option(const State0 &s);
  static std::pair<List<State0>, List<uint64_t>> inline_list(const State0 &s);
};

#endif // INCLUDED_CONSTRUCTOR_BUGS
