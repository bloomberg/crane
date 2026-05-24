#ifndef INCLUDED_CONSTRUCTOR_BUGS
#define INCLUDED_CONSTRUCTOR_BUGS

#include <any>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

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
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename A> struct Sig {
  // DATA
  A x;

  // ACCESSORS
  Sig<A> clone() const { return {x}; }

  // CREATORS
  static Sig<A> exist(A x) { return {std::move(x)}; }
};

struct ConstructorBugs {
  struct field_a {
    uint64_t a_value;

    // ACCESSORS
    field_a clone() const { return field_a{this->a_value}; }
  };

  struct field_b {
    uint64_t b_value;

    // ACCESSORS
    field_b clone() const { return field_b{this->b_value}; }
  };

  struct source_state {
    field_a source_a;
    field_b source_b;
    uint64_t source_flag;

    // ACCESSORS
    source_state clone() const {
      return source_state{this->source_a, this->source_b, this->source_flag};
    }
  };

  struct packed_state {
    source_state packed_source;
    field_a packed_a;
    field_b packed_b;

    // ACCESSORS
    packed_state clone() const {
      return packed_state{this->packed_source, this->packed_a, this->packed_b};
    }
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

    // ACCESSORS
    source_state_list clone() const {
      return source_state_list{this->source_a_list, this->source_b_list,
                               this->source_flag_list};
    }
  };

  struct packed_state_list {
    source_state_list packed_source_list;
    field_a packed_a_list;
    List<field_b> packed_b_list;

    // ACCESSORS
    packed_state_list clone() const {
      return packed_state_list{this->packed_source_list, this->packed_a_list,
                               this->packed_b_list};
    }
  };

  static source_state_list step_list(source_state_list s);
  static std::pair<bool, packed_state_list>
  bad_branch_list(const source_state_list &s1);

  struct state {
    uint64_t value;
    List<uint64_t> data;

    // ACCESSORS
    state clone() const { return state{this->value, this->data}; }
  };

  static state get_state(uint64_t n);
  static std::pair<std::pair<state, state>, uint64_t>
  tuple_from_call(uint64_t n);
  static std::pair<std::pair<state, uint64_t>,
                   std::pair<uint64_t, List<uint64_t>>>
  nested_tuples(state s);
  static std::pair<std::pair<state, uint64_t>, List<uint64_t>>
  conditional_tuple(bool b, uint64_t n);
  static uint64_t extract_value(const state &s);
  static List<uint64_t> extract_data(const state &s);
  static std::pair<std::pair<state, uint64_t>, List<uint64_t>>
  multi_call_tuple(uint64_t n);
  static std::pair<uint64_t, std::pair<state, uint64_t>> pair_test(uint64_t n);
  static std::optional<std::pair<state, uint64_t>>
  match_test(const std::optional<state> &o);
  static List<state> list_test(state s);
  static std::pair<std::pair<std::pair<state, uint64_t>,
                             std::pair<uint64_t, List<uint64_t>>>,
                   List<uint64_t>>
  triple_proj(state s);
  static std::pair<state, uint64_t> inner_pair(state s);
  static std::pair<state, uint64_t> outer_call(uint64_t n);
  static std::pair<
      std::pair<std::pair<std::pair<state, state>, uint64_t>, uint64_t>,
      List<uint64_t>>
  extreme_reuse(state s);

  struct Inner {
    uint64_t inner_val;

    // ACCESSORS
    Inner clone() const { return Inner{this->inner_val}; }
  };

  struct Outer {
    Inner outer_inner;
    uint64_t outer_data;

    // ACCESSORS
    Outer clone() const { return Outer{this->outer_inner, this->outer_data}; }
  };

  static Outer nested_record(Inner i);
  static Outer self_referential(const Outer &o);
  static std::pair<Inner, uint64_t> pair_with_proj(Inner i);
  static std::pair<std::pair<Inner, uint64_t>, std::pair<uint64_t, uint64_t>>
  nested_pairs(Inner i);
  static std::pair<Inner, Inner> pair_duplicate(Inner i);
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
  static std::pair<Inner, uint64_t> with_cast(Inner i);
  static std::pair<std::pair<Inner, uint64_t>, std::pair<Inner, uint64_t>>
  chain_lets(const Inner &i1);

  struct Container {
    Outer cont_outer;

    // ACCESSORS
    Container clone() const { return Container{this->cont_outer}; }
  };

  static std::pair<std::pair<Outer, Inner>, uint64_t>
  deep_proj(const Container &c);
  static std::pair<List<Inner>, uint64_t> list_with_proj(Inner i);
  static std::pair<Inner, uint64_t> tail_pair(Inner i, bool b);
  static std::pair<std::pair<Inner, Inner>, std::pair<uint64_t, uint64_t>>
  quad_tuple(Inner i);
  static std::pair<std::optional<Inner>, uint64_t>
  match_both_branches(const std::optional<Inner> &o);
  static Sig<Inner> sigma_test(Inner i);
  static uint64_t extract(const Inner &i);
  static std::pair<Inner, uint64_t> nested_extract(Inner i);
  static std::pair<Outer, uint64_t> update_test(const Outer &o);

  struct State {
    uint64_t value_inline;
    uint64_t data_inline;
    uint64_t flag;

    // ACCESSORS
    State clone() const {
      return State{this->value_inline, this->data_inline, this->flag};
    }
  };

  static std::pair<State, uint64_t> inline_pair(State s);
  static std::pair<std::pair<State, uint64_t>, uint64_t> inline_triple(State s);
  static std::pair<std::pair<State, uint64_t>, uint64_t> inline_nested(State s);
  static State get_state_inline(uint64_t n);
  static std::pair<State, uint64_t> inline_from_call(uint64_t n);
  static std::pair<std::pair<State, uint64_t>, uint64_t>
  same_call_multi_proj(uint64_t n);
  static std::optional<std::pair<State, uint64_t>>
  inline_match(const std::optional<State> &o);
  static std::pair<State, uint64_t> inline_if(bool b, State s);

  struct OuterInline {
    State outer_state;
    uint64_t outer_num;

    // ACCESSORS
    OuterInline clone() const {
      return OuterInline{this->outer_state, this->outer_num};
    }
  };

  static std::pair<std::pair<OuterInline, State>, uint64_t>
  inline_deep(OuterInline o);
  static std::pair<State, uint64_t> inline_double_proj(const OuterInline &o);
  static std::pair<std::pair<State, uint64_t>, std::pair<uint64_t, uint64_t>>
  inline_many(State s);
  static std::pair<std::pair<uint64_t, State>, uint64_t>
  inline_pattern(State s);
  static List<std::pair<State, uint64_t>> inline_recursive(uint64_t n, State s);
  static std::pair<std::pair<std::pair<State, uint64_t>, uint64_t>,
                   std::pair<uint64_t, State>>
  inline_complex(State s);
  static std::pair<std::pair<State, State>, std::pair<uint64_t, uint64_t>>
  inline_quad(State s);
  static std::pair<State, uint64_t> inline_both_branches(bool b, State s);

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, State &>
  static std::pair<std::pair<State, uint64_t>, uint64_t> apply_twice(F0 &&f,
                                                                     State s) {
    return std::make_pair(std::make_pair(s, f(s)), f(s));
  }

  static std::pair<std::pair<State, uint64_t>, uint64_t>
  test_apply(const State &s);
  static uint64_t get_value_inline(const State &s);
  static uint64_t get_data_inline(const State &s);
  static std::pair<std::pair<State, uint64_t>, uint64_t>
  inline_nested_calls(State s);
  static std::pair<std::optional<State>, std::optional<uint64_t>>
  inline_option(State s);
  static std::pair<List<State>, List<uint64_t>> inline_list(State s);
};

#endif // INCLUDED_CONSTRUCTOR_BUGS
