#include "constructor_bugs.h"

ConstructorBugs::source_state
ConstructorBugs::step(ConstructorBugs::source_state s) {
  return s;
}

std::pair<bool, ConstructorBugs::packed_state>
ConstructorBugs::bad_branch(const ConstructorBugs::source_state &s1) {
  ConstructorBugs::source_state s2 = step(s1);
  if (s2.source_flag == UINT64_C(0)) {
    return std::make_pair(false, packed_state{s2, s2.source_a, s2.source_b});
  } else {
    return std::make_pair(false, packed_state{s2, s2.source_a, s2.source_b});
  }
}

std::pair<bool, ConstructorBugs::packed_state>
ConstructorBugs::bad_direct(const ConstructorBugs::source_state &s1) {
  ConstructorBugs::source_state s2 = step(s1);
  return std::make_pair(false, packed_state{s2, s2.source_a, s2.source_b});
}

ConstructorBugs::source_state
ConstructorBugs::step2(const ConstructorBugs::source_state &s) {
  return source_state{s.source_a, s.source_b, (s.source_flag + UINT64_C(1))};
}

std::pair<bool, ConstructorBugs::packed_state>
ConstructorBugs::bad_complex_step(const ConstructorBugs::source_state &s1) {
  ConstructorBugs::source_state s2 = step2(s1);
  if (s2.source_flag == UINT64_C(0)) {
    return std::make_pair(false, packed_state{s2, s2.source_a, s2.source_b});
  } else {
    return std::make_pair(false, packed_state{s2, s2.source_a, s2.source_b});
  }
}

std::pair<bool, ConstructorBugs::packed_state>
ConstructorBugs::bad_nested(const ConstructorBugs::source_state &s1) {
  ConstructorBugs::source_state s2 = step(s1);
  ConstructorBugs::source_state s3 = step(std::move(s2));
  return std::make_pair(false, packed_state{s3, s3.source_a, s3.source_b});
}

ConstructorBugs::source_state_list
ConstructorBugs::step_list(ConstructorBugs::source_state_list s) {
  return s;
}

std::pair<bool, ConstructorBugs::packed_state_list>
ConstructorBugs::bad_branch_list(const ConstructorBugs::source_state_list &s1) {
  ConstructorBugs::source_state_list s2 = step_list(s1);
  if (s2.source_flag_list == UINT64_C(0)) {
    return std::make_pair(
        false, packed_state_list{s2, s2.source_a_list, s2.source_b_list});
  } else {
    return std::make_pair(
        false, packed_state_list{s2, s2.source_a_list, s2.source_b_list});
  }
}

ConstructorBugs::state ConstructorBugs::get_state(uint64_t n) {
  return state{n, List<uint64_t>::cons(
                      n, List<uint64_t>::cons(
                             (n + UINT64_C(1)),
                             List<uint64_t>::cons((n + UINT64_C(2)),
                                                  List<uint64_t>::nil())))};
}

std::pair<std::pair<ConstructorBugs::state, ConstructorBugs::state>, uint64_t>
ConstructorBugs::tuple_from_call(uint64_t n) {
  ConstructorBugs::state s = get_state(n);
  return std::make_pair(std::make_pair(s, s), s.value);
}

std::pair<std::pair<ConstructorBugs::state, uint64_t>,
          std::pair<uint64_t, List<uint64_t>>>
ConstructorBugs::nested_tuples(ConstructorBugs::state s) {
  return std::make_pair(std::make_pair(s, s.value),
                        std::make_pair(s.value, s.data));
}

std::pair<std::pair<ConstructorBugs::state, uint64_t>, List<uint64_t>>
ConstructorBugs::conditional_tuple(bool b, uint64_t n) {
  ConstructorBugs::state s = get_state(n);
  if (b) {
    return std::make_pair(std::make_pair(s, s.value), s.data);
  } else {
    return std::make_pair(std::make_pair(s, s.value), s.data);
  }
}

uint64_t ConstructorBugs::extract_value(const ConstructorBugs::state &s) {
  return s.value;
}

List<uint64_t> ConstructorBugs::extract_data(const ConstructorBugs::state &s) {
  return s.data;
}

std::pair<std::pair<ConstructorBugs::state, uint64_t>, List<uint64_t>>
ConstructorBugs::multi_call_tuple(uint64_t n) {
  ConstructorBugs::state s = get_state(n);
  return std::make_pair(std::make_pair(s, extract_value(s)), extract_data(s));
}

std::pair<uint64_t, std::pair<ConstructorBugs::state, uint64_t>>
ConstructorBugs::pair_test(uint64_t n) {
  ConstructorBugs::state s = get_state(n);
  return std::make_pair(std::move(n), std::make_pair(s, s.value));
}

std::optional<std::pair<ConstructorBugs::state, uint64_t>>
ConstructorBugs::match_test(const std::optional<ConstructorBugs::state> &o) {
  if (o.has_value()) {
    const ConstructorBugs::state &s = *o;
    return std::make_optional<std::pair<ConstructorBugs::state, uint64_t>>(
        std::make_pair(s, s.value));
  } else {
    return std::optional<std::pair<ConstructorBugs::state, uint64_t>>();
  }
}

List<ConstructorBugs::state>
ConstructorBugs::list_test(ConstructorBugs::state s) {
  return List<ConstructorBugs::state>::cons(
      s, List<ConstructorBugs::state>::cons(
             s, List<ConstructorBugs::state>::cons(
                    s, List<ConstructorBugs::state>::nil())));
}

std::pair<std::pair<std::pair<ConstructorBugs::state, uint64_t>,
                    std::pair<uint64_t, List<uint64_t>>>,
          List<uint64_t>>
ConstructorBugs::triple_proj(ConstructorBugs::state s) {
  return std::make_pair(std::make_pair(std::make_pair(s, s.value),
                                       std::make_pair(s.value, s.data)),
                        s.data);
}

std::pair<ConstructorBugs::state, uint64_t>
ConstructorBugs::inner_pair(ConstructorBugs::state s) {
  return std::make_pair(s, s.value);
}

std::pair<ConstructorBugs::state, uint64_t>
ConstructorBugs::outer_call(uint64_t n) {
  return inner_pair(get_state(n));
}

std::pair<
    std::pair<
        std::pair<std::pair<ConstructorBugs::state, ConstructorBugs::state>,
                  uint64_t>,
        uint64_t>,
    List<uint64_t>>
ConstructorBugs::extreme_reuse(ConstructorBugs::state s) {
  return std::make_pair(
      std::make_pair(std::make_pair(std::make_pair(s, s), s.value), s.value),
      s.data);
}

ConstructorBugs::Outer
ConstructorBugs::nested_record(ConstructorBugs::Inner i) {
  return Outer{i, i.inner_val};
}

ConstructorBugs::Outer
ConstructorBugs::self_referential(const ConstructorBugs::Outer &o) {
  return Outer{o.outer_inner, o.outer_inner.inner_val};
}

std::pair<ConstructorBugs::Inner, uint64_t>
ConstructorBugs::pair_with_proj(ConstructorBugs::Inner i) {
  return std::make_pair(i, i.inner_val);
}

std::pair<std::pair<ConstructorBugs::Inner, uint64_t>,
          std::pair<uint64_t, uint64_t>>
ConstructorBugs::nested_pairs(ConstructorBugs::Inner i) {
  return std::make_pair(std::make_pair(i, i.inner_val),
                        std::make_pair(i.inner_val, i.inner_val));
}

std::pair<ConstructorBugs::Inner, ConstructorBugs::Inner>
ConstructorBugs::pair_duplicate(ConstructorBugs::Inner i) {
  return std::make_pair(i, i);
}

ConstructorBugs::Inner ConstructorBugs::mk_inner(uint64_t n) {
  return Inner{n};
}

std::pair<ConstructorBugs::Inner, uint64_t>
ConstructorBugs::pair_from_func(uint64_t n) {
  ConstructorBugs::Inner i = mk_inner(n);
  return std::make_pair(i, i.inner_val);
}

std::optional<std::pair<ConstructorBugs::Inner, uint64_t>>
ConstructorBugs::match_option_record(
    const std::optional<ConstructorBugs::Inner> &o) {
  if (o.has_value()) {
    const ConstructorBugs::Inner &i = *o;
    return std::make_optional<std::pair<ConstructorBugs::Inner, uint64_t>>(
        std::make_pair(i, i.inner_val));
  } else {
    return std::optional<std::pair<ConstructorBugs::Inner, uint64_t>>();
  }
}

std::pair<ConstructorBugs::Inner, uint64_t>
ConstructorBugs::match_sum(const ConstructorBugs::MySum &s) {
  if (std::holds_alternative<typename ConstructorBugs::MySum::Left>(s.v())) {
    const auto &[a0] = std::get<typename ConstructorBugs::MySum::Left>(s.v());
    return std::make_pair(a0, a0.inner_val);
  } else {
    const auto &[a0] = std::get<typename ConstructorBugs::MySum::Right>(s.v());
    return std::make_pair(Inner{a0}, a0);
  }
}

std::pair<ConstructorBugs::Inner, uint64_t>
ConstructorBugs::with_cast(ConstructorBugs::Inner i) {
  return std::make_pair(i, i.inner_val);
}

std::pair<std::pair<ConstructorBugs::Inner, uint64_t>,
          std::pair<ConstructorBugs::Inner, uint64_t>>
ConstructorBugs::chain_lets(const ConstructorBugs::Inner &i1) {
  ConstructorBugs::Inner i2 = Inner{i1.inner_val};
  ConstructorBugs::Inner i3 = Inner{i2.inner_val};
  return std::make_pair(std::make_pair(i2, i2.inner_val),
                        std::make_pair(i3, i3.inner_val));
}

std::pair<std::pair<ConstructorBugs::Outer, ConstructorBugs::Inner>, uint64_t>
ConstructorBugs::deep_proj(const ConstructorBugs::Container &c) {
  const ConstructorBugs::Outer &o = c.cont_outer;
  const ConstructorBugs::Inner &i = o.outer_inner;
  return std::make_pair(std::make_pair(o, i), i.inner_val);
}

std::pair<List<ConstructorBugs::Inner>, uint64_t>
ConstructorBugs::list_with_proj(ConstructorBugs::Inner i) {
  return std::make_pair(
      List<ConstructorBugs::Inner>::cons(
          i, List<ConstructorBugs::Inner>::cons(
                 i, List<ConstructorBugs::Inner>::cons(
                        i, List<ConstructorBugs::Inner>::nil()))),
      i.inner_val);
}

std::pair<ConstructorBugs::Inner, uint64_t>
ConstructorBugs::tail_pair(ConstructorBugs::Inner i, bool b) {
  if (b) {
    return std::make_pair(i, i.inner_val);
  } else {
    return std::make_pair(std::move(i), UINT64_C(0));
  }
}

std::pair<std::pair<ConstructorBugs::Inner, ConstructorBugs::Inner>,
          std::pair<uint64_t, uint64_t>>
ConstructorBugs::quad_tuple(ConstructorBugs::Inner i) {
  return std::make_pair(std::make_pair(i, i),
                        std::make_pair(i.inner_val, i.inner_val));
}

std::pair<std::optional<ConstructorBugs::Inner>, uint64_t>
ConstructorBugs::match_both_branches(
    const std::optional<ConstructorBugs::Inner> &o) {
  if (o.has_value()) {
    const ConstructorBugs::Inner &i = *o;
    return std::make_pair(std::make_optional<ConstructorBugs::Inner>(i),
                          i.inner_val);
  } else {
    return std::make_pair(std::optional<ConstructorBugs::Inner>(), UINT64_C(0));
  }
}

Sig<ConstructorBugs::Inner>
ConstructorBugs::sigma_test(ConstructorBugs::Inner i) {
  return Sig<ConstructorBugs::Inner>::exist(std::move(i));
}

uint64_t ConstructorBugs::extract(const ConstructorBugs::Inner &i) {
  return i.inner_val;
}

std::pair<ConstructorBugs::Inner, uint64_t>
ConstructorBugs::nested_extract(ConstructorBugs::Inner i) {
  return std::make_pair(i, extract(i));
}

std::pair<ConstructorBugs::Outer, uint64_t>
ConstructorBugs::update_test(const ConstructorBugs::Outer &o) {
  return std::make_pair(Outer{o.outer_inner, (o.outer_data + UINT64_C(1))},
                        o.outer_inner.inner_val);
}

std::pair<ConstructorBugs::State, uint64_t>
ConstructorBugs::inline_pair(ConstructorBugs::State s) {
  return std::make_pair(s, s.value_inline);
}

std::pair<std::pair<ConstructorBugs::State, uint64_t>, uint64_t>
ConstructorBugs::inline_triple(ConstructorBugs::State s) {
  return std::make_pair(std::make_pair(s, s.value_inline), s.data_inline);
}

std::pair<std::pair<ConstructorBugs::State, uint64_t>, uint64_t>
ConstructorBugs::inline_nested(ConstructorBugs::State s) {
  return std::make_pair(std::make_pair(s, s.value_inline), s.data_inline);
}

ConstructorBugs::State ConstructorBugs::get_state_inline(uint64_t n) {
  return State{n, n, n};
}

std::pair<ConstructorBugs::State, uint64_t>
ConstructorBugs::inline_from_call(uint64_t n) {
  return std::make_pair(get_state_inline(n), get_state_inline(n).value_inline);
}

std::pair<std::pair<ConstructorBugs::State, uint64_t>, uint64_t>
ConstructorBugs::same_call_multi_proj(uint64_t n) {
  return std::make_pair(
      std::make_pair(get_state_inline(n), get_state_inline(n).value_inline),
      get_state_inline(n).data_inline);
}

std::optional<std::pair<ConstructorBugs::State, uint64_t>>
ConstructorBugs::inline_match(const std::optional<ConstructorBugs::State> &o) {
  if (o.has_value()) {
    const ConstructorBugs::State &s = *o;
    return std::make_optional<std::pair<ConstructorBugs::State, uint64_t>>(
        std::make_pair(s, s.value_inline));
  } else {
    return std::optional<std::pair<ConstructorBugs::State, uint64_t>>();
  }
}

std::pair<ConstructorBugs::State, uint64_t>
ConstructorBugs::inline_if(bool b, ConstructorBugs::State s) {
  if (b) {
    return std::make_pair(s, s.value_inline);
  } else {
    return std::make_pair(std::move(s), UINT64_C(0));
  }
}

std::pair<std::pair<ConstructorBugs::OuterInline, ConstructorBugs::State>,
          uint64_t>
ConstructorBugs::inline_deep(ConstructorBugs::OuterInline o) {
  return std::make_pair(std::make_pair(o, o.outer_state),
                        o.outer_state.value_inline);
}

std::pair<ConstructorBugs::State, uint64_t>
ConstructorBugs::inline_double_proj(const ConstructorBugs::OuterInline &o) {
  return std::make_pair(o.outer_state, o.outer_state.value_inline);
}

std::pair<std::pair<ConstructorBugs::State, uint64_t>,
          std::pair<uint64_t, uint64_t>>
ConstructorBugs::inline_many(ConstructorBugs::State s) {
  return std::make_pair(std::make_pair(s, s.value_inline),
                        std::make_pair(s.data_inline, s.flag));
}

std::pair<std::pair<uint64_t, ConstructorBugs::State>, uint64_t>
ConstructorBugs::inline_pattern(ConstructorBugs::State s) {
  uint64_t v = s.value_inline;
  uint64_t d = s.data_inline;
  std::any _x = s.flag;
  return std::make_pair(std::make_pair(v, s), d);
}

List<std::pair<ConstructorBugs::State, uint64_t>>
ConstructorBugs::inline_recursive(uint64_t n, ConstructorBugs::State s) {
  if (n <= 0) {
    return List<std::pair<ConstructorBugs::State, uint64_t>>::nil();
  } else {
    uint64_t m = n - 1;
    return List<std::pair<ConstructorBugs::State, uint64_t>>::cons(
        std::make_pair(s, s.value_inline), inline_recursive(m, s));
  }
}

std::pair<std::pair<std::pair<ConstructorBugs::State, uint64_t>, uint64_t>,
          std::pair<uint64_t, ConstructorBugs::State>>
ConstructorBugs::inline_complex(ConstructorBugs::State s) {
  return std::make_pair(
      std::make_pair(std::make_pair(s, s.value_inline), s.data_inline),
      std::make_pair(s.flag, s));
}

std::pair<std::pair<ConstructorBugs::State, ConstructorBugs::State>,
          std::pair<uint64_t, uint64_t>>
ConstructorBugs::inline_quad(ConstructorBugs::State s) {
  return std::make_pair(std::make_pair(s, s),
                        std::make_pair(s.value_inline, s.data_inline));
}

std::pair<ConstructorBugs::State, uint64_t>
ConstructorBugs::inline_both_branches(bool b, ConstructorBugs::State s) {
  if (b) {
    return std::make_pair(s, s.value_inline);
  } else {
    return std::make_pair(s, s.value_inline);
  }
}

std::pair<std::pair<ConstructorBugs::State, uint64_t>, uint64_t>
ConstructorBugs::test_apply(const ConstructorBugs::State &s) {
  return apply_twice(
      [](const ConstructorBugs::State &s0) { return s0.value_inline; }, s);
}

uint64_t ConstructorBugs::get_value_inline(const ConstructorBugs::State &s) {
  return s.value_inline;
}

uint64_t ConstructorBugs::get_data_inline(const ConstructorBugs::State &s) {
  return s.data_inline;
}

std::pair<std::pair<ConstructorBugs::State, uint64_t>, uint64_t>
ConstructorBugs::inline_nested_calls(ConstructorBugs::State s) {
  return std::make_pair(std::make_pair(s, get_value_inline(s)),
                        get_data_inline(s));
}

std::pair<std::optional<ConstructorBugs::State>, std::optional<uint64_t>>
ConstructorBugs::inline_option(ConstructorBugs::State s) {
  return std::make_pair(std::make_optional<ConstructorBugs::State>(s),
                        std::make_optional<uint64_t>(s.value_inline));
}

std::pair<List<ConstructorBugs::State>, List<uint64_t>>
ConstructorBugs::inline_list(ConstructorBugs::State s) {
  return std::make_pair(
      List<ConstructorBugs::State>::cons(s,
                                         List<ConstructorBugs::State>::nil()),
      List<uint64_t>::cons(s.value_inline, List<uint64_t>::nil()));
}
