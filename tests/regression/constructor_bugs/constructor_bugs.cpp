#include <constructor_bugs.h>

#include <any>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) ConstructorBugs::source_state
ConstructorBugs::step(ConstructorBugs::source_state s) {
  return s;
}

__attribute__((pure)) std::pair<bool, ConstructorBugs::packed_state>
ConstructorBugs::bad_branch(const ConstructorBugs::source_state &s1) {
  ConstructorBugs::source_state s2 = step(s1);
  if (s2.source_flag == 0u) {
    return std::make_pair(false, packed_state{s2, s2.source_a, s2.source_b});
  } else {
    return std::make_pair(false, packed_state{s2, s2.source_a, s2.source_b});
  }
}

__attribute__((pure)) std::pair<bool, ConstructorBugs::packed_state>
ConstructorBugs::bad_direct(const ConstructorBugs::source_state &s1) {
  ConstructorBugs::source_state s2 = step(s1);
  return std::make_pair(false, packed_state{s2, s2.source_a, s2.source_b});
}

__attribute__((pure)) ConstructorBugs::source_state
ConstructorBugs::step2(const ConstructorBugs::source_state &s) {
  return source_state{s.source_a, s.source_b, (s.source_flag + 1u)};
}

__attribute__((pure)) std::pair<bool, ConstructorBugs::packed_state>
ConstructorBugs::bad_complex_step(const ConstructorBugs::source_state &s1) {
  ConstructorBugs::source_state s2 = step2(s1);
  if (s2.source_flag == 0u) {
    return std::make_pair(false, packed_state{s2, s2.source_a, s2.source_b});
  } else {
    return std::make_pair(false, packed_state{s2, s2.source_a, s2.source_b});
  }
}

__attribute__((pure)) std::pair<bool, ConstructorBugs::packed_state>
ConstructorBugs::bad_nested(const ConstructorBugs::source_state &s1) {
  ConstructorBugs::source_state s2 = step(s1);
  ConstructorBugs::source_state s3 = step(s2);
  return std::make_pair(false, packed_state{s3, s3.source_a, s3.source_b});
}

__attribute__((pure)) ConstructorBugs::source_state_list
ConstructorBugs::step_list(ConstructorBugs::source_state_list s) {
  return s;
}

__attribute__((pure)) std::pair<bool, ConstructorBugs::packed_state_list>
ConstructorBugs::bad_branch_list(const ConstructorBugs::source_state_list &s1) {
  ConstructorBugs::source_state_list s2 = step_list(s1);
  if (s2.source_flag_list == 0u) {
    return std::make_pair(
        false, packed_state_list{s2, s2.source_a_list, s2.source_b_list});
  } else {
    return std::make_pair(
        false, packed_state_list{s2, s2.source_a_list, s2.source_b_list});
  }
}

__attribute__((pure)) ConstructorBugs::state
ConstructorBugs::get_state(unsigned int n) {
  return state{n,
               List<unsigned int>::cons(
                   n, List<unsigned int>::cons(
                          (n + 1u), List<unsigned int>::cons(
                                        (n + 2u), List<unsigned int>::nil())))};
}

__attribute__((pure))
std::pair<std::pair<ConstructorBugs::state, ConstructorBugs::state>,
          unsigned int>
ConstructorBugs::tuple_from_call(const unsigned int &n) {
  ConstructorBugs::state s = get_state(n);
  return std::make_pair(std::make_pair(s, s), s.value);
}

__attribute__((pure)) std::pair<std::pair<ConstructorBugs::state, unsigned int>,
                                std::pair<unsigned int, List<unsigned int>>>
ConstructorBugs::nested_tuples(ConstructorBugs::state s) {
  return std::make_pair(std::make_pair(s, s.value),
                        std::make_pair(s.value, s.data));
}

__attribute__((pure))
std::pair<std::pair<ConstructorBugs::state, unsigned int>, List<unsigned int>>
ConstructorBugs::conditional_tuple(const bool &b, const unsigned int &n) {
  ConstructorBugs::state s = get_state(n);
  if (b) {
    return std::make_pair(std::make_pair(s, s.value), s.data);
  } else {
    return std::make_pair(std::make_pair(s, s.value), s.data);
  }
}

__attribute__((pure)) unsigned int
ConstructorBugs::extract_value(const ConstructorBugs::state &s) {
  return s.value;
}

__attribute__((pure)) List<unsigned int>
ConstructorBugs::extract_data(const ConstructorBugs::state &s) {
  return s.data;
}

__attribute__((pure))
std::pair<std::pair<ConstructorBugs::state, unsigned int>, List<unsigned int>>
ConstructorBugs::multi_call_tuple(const unsigned int &n) {
  ConstructorBugs::state s = get_state(n);
  return std::make_pair(std::make_pair(s, extract_value(s)), extract_data(s));
}

__attribute__((pure))
std::pair<unsigned int, std::pair<ConstructorBugs::state, unsigned int>>
ConstructorBugs::pair_test(unsigned int n) {
  ConstructorBugs::state s = get_state(n);
  return std::make_pair(n, std::make_pair(s, s.value));
}

__attribute__((pure))
std::optional<std::pair<ConstructorBugs::state, unsigned int>>
ConstructorBugs::match_test(const std::optional<ConstructorBugs::state> &o) {
  if (o.has_value()) {
    const ConstructorBugs::state &s = *o;
    return std::make_optional<std::pair<ConstructorBugs::state, unsigned int>>(
        std::make_pair(s, s.value));
  } else {
    return std::optional<std::pair<ConstructorBugs::state, unsigned int>>();
  }
}

__attribute__((pure)) List<ConstructorBugs::state>
ConstructorBugs::list_test(ConstructorBugs::state s) {
  return List<ConstructorBugs::state>::cons(
      s, List<ConstructorBugs::state>::cons(
             s, List<ConstructorBugs::state>::cons(
                    s, List<ConstructorBugs::state>::nil())));
}

__attribute__((pure))
std::pair<std::pair<std::pair<ConstructorBugs::state, unsigned int>,
                    std::pair<unsigned int, List<unsigned int>>>,
          List<unsigned int>>
ConstructorBugs::triple_proj(ConstructorBugs::state s) {
  return std::make_pair(std::make_pair(std::make_pair(s, s.value),
                                       std::make_pair(s.value, s.data)),
                        s.data);
}

__attribute__((pure)) std::pair<ConstructorBugs::state, unsigned int>
ConstructorBugs::inner_pair(ConstructorBugs::state s) {
  return std::make_pair(s, s.value);
}

__attribute__((pure)) std::pair<ConstructorBugs::state, unsigned int>
ConstructorBugs::outer_call(const unsigned int &n) {
  return inner_pair(get_state(n));
}

__attribute__((pure)) std::pair<
    std::pair<
        std::pair<std::pair<ConstructorBugs::state, ConstructorBugs::state>,
                  unsigned int>,
        unsigned int>,
    List<unsigned int>>
ConstructorBugs::extreme_reuse(ConstructorBugs::state s) {
  return std::make_pair(
      std::make_pair(std::make_pair(std::make_pair(s, s), s.value), s.value),
      s.data);
}

__attribute__((pure)) ConstructorBugs::Outer
ConstructorBugs::nested_record(ConstructorBugs::Inner i) {
  return Outer{i, i.inner_val};
}

__attribute__((pure)) ConstructorBugs::Outer
ConstructorBugs::self_referential(const ConstructorBugs::Outer &o) {
  return Outer{o.outer_inner, o.outer_inner.inner_val};
}

__attribute__((pure)) std::pair<ConstructorBugs::Inner, unsigned int>
ConstructorBugs::pair_with_proj(ConstructorBugs::Inner i) {
  return std::make_pair(i, i.inner_val);
}

__attribute__((pure)) std::pair<std::pair<ConstructorBugs::Inner, unsigned int>,
                                std::pair<unsigned int, unsigned int>>
ConstructorBugs::nested_pairs(ConstructorBugs::Inner i) {
  return std::make_pair(std::make_pair(i, i.inner_val),
                        std::make_pair(i.inner_val, i.inner_val));
}

__attribute__((pure)) std::pair<ConstructorBugs::Inner, ConstructorBugs::Inner>
ConstructorBugs::pair_duplicate(ConstructorBugs::Inner i) {
  return std::make_pair(i, i);
}

__attribute__((pure)) ConstructorBugs::Inner
ConstructorBugs::mk_inner(unsigned int n) {
  return Inner{n};
}

__attribute__((pure)) std::pair<ConstructorBugs::Inner, unsigned int>
ConstructorBugs::pair_from_func(const unsigned int &n) {
  ConstructorBugs::Inner i = mk_inner(n);
  return std::make_pair(i, i.inner_val);
}

__attribute__((pure))
std::optional<std::pair<ConstructorBugs::Inner, unsigned int>>
ConstructorBugs::match_option_record(
    const std::optional<ConstructorBugs::Inner> &o) {
  if (o.has_value()) {
    const ConstructorBugs::Inner &i = *o;
    return std::make_optional<std::pair<ConstructorBugs::Inner, unsigned int>>(
        std::make_pair(i, i.inner_val));
  } else {
    return std::optional<std::pair<ConstructorBugs::Inner, unsigned int>>();
  }
}

__attribute__((pure)) std::pair<ConstructorBugs::Inner, unsigned int>
ConstructorBugs::match_sum(const ConstructorBugs::MySum &s) {
  if (std::holds_alternative<typename ConstructorBugs::MySum::Left>(s.v())) {
    const auto &[d_a0] = std::get<typename ConstructorBugs::MySum::Left>(s.v());
    return std::make_pair(d_a0, d_a0.inner_val);
  } else {
    const auto &[d_a0] =
        std::get<typename ConstructorBugs::MySum::Right>(s.v());
    return std::make_pair(Inner{d_a0}, d_a0);
  }
}

__attribute__((pure)) std::pair<ConstructorBugs::Inner, unsigned int>
ConstructorBugs::with_cast(ConstructorBugs::Inner i) {
  return std::make_pair(i, i.inner_val);
}

__attribute__((pure)) std::pair<std::pair<ConstructorBugs::Inner, unsigned int>,
                                std::pair<ConstructorBugs::Inner, unsigned int>>
ConstructorBugs::chain_lets(const ConstructorBugs::Inner &i1) {
  ConstructorBugs::Inner i2 = Inner{i1.inner_val};
  ConstructorBugs::Inner i3 = Inner{i2.inner_val};
  return std::make_pair(std::make_pair(i2, i2.inner_val),
                        std::make_pair(i3, i3.inner_val));
}

__attribute__((pure))
std::pair<std::pair<ConstructorBugs::Outer, ConstructorBugs::Inner>,
          unsigned int>
ConstructorBugs::deep_proj(const ConstructorBugs::Container &c) {
  const ConstructorBugs::Outer &o = c.cont_outer;
  const ConstructorBugs::Inner &i = o.outer_inner;
  return std::make_pair(std::make_pair(o, i), i.inner_val);
}

__attribute__((pure)) std::pair<List<ConstructorBugs::Inner>, unsigned int>
ConstructorBugs::list_with_proj(ConstructorBugs::Inner i) {
  return std::make_pair(
      List<ConstructorBugs::Inner>::cons(
          i, List<ConstructorBugs::Inner>::cons(
                 i, List<ConstructorBugs::Inner>::cons(
                        i, List<ConstructorBugs::Inner>::nil()))),
      i.inner_val);
}

__attribute__((pure)) std::pair<ConstructorBugs::Inner, unsigned int>
ConstructorBugs::tail_pair(ConstructorBugs::Inner i, const bool &b) {
  if (b) {
    return std::make_pair(i, i.inner_val);
  } else {
    return std::make_pair(i, 0u);
  }
}

__attribute__((pure))
std::pair<std::pair<ConstructorBugs::Inner, ConstructorBugs::Inner>,
          std::pair<unsigned int, unsigned int>>
ConstructorBugs::quad_tuple(ConstructorBugs::Inner i) {
  return std::make_pair(std::make_pair(i, i),
                        std::make_pair(i.inner_val, i.inner_val));
}

__attribute__((pure))
std::pair<std::optional<ConstructorBugs::Inner>, unsigned int>
ConstructorBugs::match_both_branches(
    const std::optional<ConstructorBugs::Inner> &o) {
  if (o.has_value()) {
    const ConstructorBugs::Inner &i = *o;
    return std::make_pair(std::make_optional<ConstructorBugs::Inner>(i),
                          i.inner_val);
  } else {
    return std::make_pair(std::optional<ConstructorBugs::Inner>(), 0u);
  }
}

__attribute__((pure)) Sig<ConstructorBugs::Inner>
ConstructorBugs::sigma_test(ConstructorBugs::Inner i) {
  return Sig<ConstructorBugs::Inner>::exist(i);
}

__attribute__((pure)) unsigned int
ConstructorBugs::extract(const ConstructorBugs::Inner &i) {
  return i.inner_val;
}

__attribute__((pure)) std::pair<ConstructorBugs::Inner, unsigned int>
ConstructorBugs::nested_extract(ConstructorBugs::Inner i) {
  return std::make_pair(i, extract(i));
}

__attribute__((pure)) std::pair<ConstructorBugs::Outer, unsigned int>
ConstructorBugs::update_test(const ConstructorBugs::Outer &o) {
  return std::make_pair(Outer{o.outer_inner, (o.outer_data + 1u)},
                        o.outer_inner.inner_val);
}

__attribute__((pure)) std::pair<ConstructorBugs::State, unsigned int>
ConstructorBugs::inline_pair(ConstructorBugs::State s) {
  return std::make_pair(s, s.value_inline);
}

__attribute__((pure))
std::pair<std::pair<ConstructorBugs::State, unsigned int>, unsigned int>
ConstructorBugs::inline_triple(ConstructorBugs::State s) {
  return std::make_pair(std::make_pair(s, s.value_inline), s.data_inline);
}

__attribute__((pure))
std::pair<std::pair<ConstructorBugs::State, unsigned int>, unsigned int>
ConstructorBugs::inline_nested(ConstructorBugs::State s) {
  return std::make_pair(std::make_pair(s, s.value_inline), s.data_inline);
}

__attribute__((pure)) ConstructorBugs::State
ConstructorBugs::get_state_inline(unsigned int n) {
  return State{n, n, n};
}

__attribute__((pure)) std::pair<ConstructorBugs::State, unsigned int>
ConstructorBugs::inline_from_call(const unsigned int &n) {
  return std::make_pair(get_state_inline(n), get_state_inline(n).value_inline);
}

__attribute__((pure))
std::pair<std::pair<ConstructorBugs::State, unsigned int>, unsigned int>
ConstructorBugs::same_call_multi_proj(const unsigned int &n) {
  return std::make_pair(
      std::make_pair(get_state_inline(n), get_state_inline(n).value_inline),
      get_state_inline(n).data_inline);
}

__attribute__((pure))
std::optional<std::pair<ConstructorBugs::State, unsigned int>>
ConstructorBugs::inline_match(const std::optional<ConstructorBugs::State> &o) {
  if (o.has_value()) {
    const ConstructorBugs::State &s = *o;
    return std::make_optional<std::pair<ConstructorBugs::State, unsigned int>>(
        std::make_pair(s, s.value_inline));
  } else {
    return std::optional<std::pair<ConstructorBugs::State, unsigned int>>();
  }
}

__attribute__((pure)) std::pair<ConstructorBugs::State, unsigned int>
ConstructorBugs::inline_if(const bool &b, ConstructorBugs::State s) {
  if (b) {
    return std::make_pair(s, s.value_inline);
  } else {
    return std::make_pair(s, 0u);
  }
}

__attribute__((pure))
std::pair<std::pair<ConstructorBugs::OuterInline, ConstructorBugs::State>,
          unsigned int>
ConstructorBugs::inline_deep(ConstructorBugs::OuterInline o) {
  return std::make_pair(std::make_pair(o, o.outer_state),
                        o.outer_state.value_inline);
}

__attribute__((pure)) std::pair<ConstructorBugs::State, unsigned int>
ConstructorBugs::inline_double_proj(const ConstructorBugs::OuterInline &o) {
  return std::make_pair(o.outer_state, o.outer_state.value_inline);
}

__attribute__((pure)) std::pair<std::pair<ConstructorBugs::State, unsigned int>,
                                std::pair<unsigned int, unsigned int>>
ConstructorBugs::inline_many(ConstructorBugs::State s) {
  return std::make_pair(std::make_pair(s, s.value_inline),
                        std::make_pair(s.data_inline, s.flag));
}

__attribute__((pure))
std::pair<std::pair<unsigned int, ConstructorBugs::State>, unsigned int>
ConstructorBugs::inline_pattern(ConstructorBugs::State s) {
  unsigned int v = s.value_inline;
  unsigned int d = s.data_inline;
  std::any _x = s.flag;
  return std::make_pair(std::make_pair(v, s), d);
}

__attribute__((pure)) List<std::pair<ConstructorBugs::State, unsigned int>>
ConstructorBugs::inline_recursive(const unsigned int &n,
                                  ConstructorBugs::State s) {
  if (n <= 0) {
    return List<std::pair<ConstructorBugs::State, unsigned int>>::nil();
  } else {
    unsigned int m = n - 1;
    return List<std::pair<ConstructorBugs::State, unsigned int>>::cons(
        std::make_pair(s, s.value_inline), inline_recursive(m, s));
  }
}

__attribute__((pure)) std::pair<
    std::pair<std::pair<ConstructorBugs::State, unsigned int>, unsigned int>,
    std::pair<unsigned int, ConstructorBugs::State>>
ConstructorBugs::inline_complex(ConstructorBugs::State s) {
  return std::make_pair(
      std::make_pair(std::make_pair(s, s.value_inline), s.data_inline),
      std::make_pair(s.flag, s));
}

__attribute__((pure))
std::pair<std::pair<ConstructorBugs::State, ConstructorBugs::State>,
          std::pair<unsigned int, unsigned int>>
ConstructorBugs::inline_quad(ConstructorBugs::State s) {
  return std::make_pair(std::make_pair(s, s),
                        std::make_pair(s.value_inline, s.data_inline));
}

__attribute__((pure)) std::pair<ConstructorBugs::State, unsigned int>
ConstructorBugs::inline_both_branches(const bool &b, ConstructorBugs::State s) {
  if (b) {
    return std::make_pair(s, s.value_inline);
  } else {
    return std::make_pair(s, s.value_inline);
  }
}

__attribute__((pure))
std::pair<std::pair<ConstructorBugs::State, unsigned int>, unsigned int>
ConstructorBugs::test_apply(const ConstructorBugs::State &s) {
  return apply_twice(
      [](const ConstructorBugs::State &s0) { return s0.value_inline; }, s);
}

__attribute__((pure)) unsigned int
ConstructorBugs::get_value_inline(const ConstructorBugs::State &s) {
  return s.value_inline;
}

__attribute__((pure)) unsigned int
ConstructorBugs::get_data_inline(const ConstructorBugs::State &s) {
  return s.data_inline;
}

__attribute__((pure))
std::pair<std::pair<ConstructorBugs::State, unsigned int>, unsigned int>
ConstructorBugs::inline_nested_calls(ConstructorBugs::State s) {
  return std::make_pair(std::make_pair(s, get_value_inline(s)),
                        get_data_inline(s));
}

__attribute__((pure))
std::pair<std::optional<ConstructorBugs::State>, std::optional<unsigned int>>
ConstructorBugs::inline_option(ConstructorBugs::State s) {
  return std::make_pair(std::make_optional<ConstructorBugs::State>(s),
                        std::make_optional<unsigned int>(s.value_inline));
}

__attribute__((pure))
std::pair<List<ConstructorBugs::State>, List<unsigned int>>
ConstructorBugs::inline_list(ConstructorBugs::State s) {
  return std::make_pair(
      List<ConstructorBugs::State>::cons(s,
                                         List<ConstructorBugs::State>::nil()),
      List<unsigned int>::cons(s.value_inline, List<unsigned int>::nil()));
}
