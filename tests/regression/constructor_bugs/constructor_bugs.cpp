#include <constructor_bugs.h>

#include <any>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<ConstructorBugs::source_state>
ConstructorBugs::step(std::shared_ptr<ConstructorBugs::source_state> s) {
  return s;
}

__attribute__((pure))
std::pair<bool, std::shared_ptr<ConstructorBugs::packed_state>>
ConstructorBugs::bad_branch(
    const std::shared_ptr<ConstructorBugs::source_state> &s1) {
  std::shared_ptr<ConstructorBugs::source_state> s2 = step(s1);
  if (s2->source_flag == 0u) {
    return std::make_pair(false,
                          std::make_shared<ConstructorBugs::packed_state>(
                              packed_state{s2, s2->source_a, s2->source_b}));
  } else {
    return std::make_pair(false,
                          std::make_shared<ConstructorBugs::packed_state>(
                              packed_state{s2, s2->source_a, s2->source_b}));
  }
}

__attribute__((pure))
std::pair<bool, std::shared_ptr<ConstructorBugs::packed_state>>
ConstructorBugs::bad_direct(
    const std::shared_ptr<ConstructorBugs::source_state> &s1) {
  std::shared_ptr<ConstructorBugs::source_state> s2 = step(s1);
  return std::make_pair(false,
                        std::make_shared<ConstructorBugs::packed_state>(
                            packed_state{s2, s2->source_a, s2->source_b}));
}

std::shared_ptr<ConstructorBugs::source_state> ConstructorBugs::step2(
    const std::shared_ptr<ConstructorBugs::source_state> &s) {
  return std::make_shared<ConstructorBugs::source_state>(
      source_state{s->source_a, s->source_b, (s->source_flag + 1u)});
}

__attribute__((pure))
std::pair<bool, std::shared_ptr<ConstructorBugs::packed_state>>
ConstructorBugs::bad_complex_step(
    const std::shared_ptr<ConstructorBugs::source_state> &s1) {
  std::shared_ptr<ConstructorBugs::source_state> s2 = step2(s1);
  if (s2->source_flag == 0u) {
    return std::make_pair(false,
                          std::make_shared<ConstructorBugs::packed_state>(
                              packed_state{s2, s2->source_a, s2->source_b}));
  } else {
    return std::make_pair(false,
                          std::make_shared<ConstructorBugs::packed_state>(
                              packed_state{s2, s2->source_a, s2->source_b}));
  }
}

__attribute__((pure))
std::pair<bool, std::shared_ptr<ConstructorBugs::packed_state>>
ConstructorBugs::bad_nested(
    const std::shared_ptr<ConstructorBugs::source_state> &s1) {
  std::shared_ptr<ConstructorBugs::source_state> s2 = step(s1);
  std::shared_ptr<ConstructorBugs::source_state> s3 = step(std::move(s2));
  return std::make_pair(false,
                        std::make_shared<ConstructorBugs::packed_state>(
                            packed_state{s3, s3->source_a, s3->source_b}));
}

std::shared_ptr<ConstructorBugs::source_state_list> ConstructorBugs::step_list(
    std::shared_ptr<ConstructorBugs::source_state_list> s) {
  return s;
}

__attribute__((pure))
std::pair<bool, std::shared_ptr<ConstructorBugs::packed_state_list>>
ConstructorBugs::bad_branch_list(
    const std::shared_ptr<ConstructorBugs::source_state_list> &s1) {
  std::shared_ptr<ConstructorBugs::source_state_list> s2 = step_list(s1);
  if (s2->source_flag_list == 0u) {
    return std::make_pair(
        false,
        std::make_shared<ConstructorBugs::packed_state_list>(
            packed_state_list{s2, s2->source_a_list, s2->source_b_list}));
  } else {
    return std::make_pair(
        false,
        std::make_shared<ConstructorBugs::packed_state_list>(
            packed_state_list{s2, s2->source_a_list, s2->source_b_list}));
  }
}

std::shared_ptr<ConstructorBugs::state>
ConstructorBugs::get_state(const unsigned int n) {
  return std::make_shared<ConstructorBugs::state>(state{
      n, List<unsigned int>::cons(
             n, List<unsigned int>::cons(
                    (n + 1u), List<unsigned int>::cons(
                                  (n + 2u), List<unsigned int>::nil())))});
}

__attribute__((pure))
std::pair<std::pair<std::shared_ptr<ConstructorBugs::state>,
                    std::shared_ptr<ConstructorBugs::state>>,
          unsigned int>
ConstructorBugs::tuple_from_call(const unsigned int n) {
  std::shared_ptr<ConstructorBugs::state> s = get_state(n);
  return std::make_pair(std::make_pair(s, s), s->value);
}

__attribute__((pure))
std::pair<std::pair<std::shared_ptr<ConstructorBugs::state>, unsigned int>,
          std::pair<unsigned int, std::shared_ptr<List<unsigned int>>>>
ConstructorBugs::nested_tuples(std::shared_ptr<ConstructorBugs::state> s) {
  return std::make_pair(std::make_pair(s, s->value),
                        std::make_pair(s->value, s->data));
}

__attribute__((pure))
std::pair<std::pair<std::shared_ptr<ConstructorBugs::state>, unsigned int>,
          std::shared_ptr<List<unsigned int>>>
ConstructorBugs::conditional_tuple(const bool b, const unsigned int n) {
  std::shared_ptr<ConstructorBugs::state> s = get_state(n);
  if (b) {
    return std::make_pair(std::make_pair(s, s->value), s->data);
  } else {
    return std::make_pair(std::make_pair(s, s->value), s->data);
  }
}

__attribute__((pure)) unsigned int ConstructorBugs::extract_value(
    const std::shared_ptr<ConstructorBugs::state> &s) {
  return s->value;
}

std::shared_ptr<List<unsigned int>> ConstructorBugs::extract_data(
    const std::shared_ptr<ConstructorBugs::state> &s) {
  return s->data;
}

__attribute__((pure))
std::pair<std::pair<std::shared_ptr<ConstructorBugs::state>, unsigned int>,
          std::shared_ptr<List<unsigned int>>>
ConstructorBugs::multi_call_tuple(const unsigned int n) {
  std::shared_ptr<ConstructorBugs::state> s = get_state(n);
  return std::make_pair(std::make_pair(s, extract_value(s)), extract_data(s));
}

__attribute__((pure))
std::pair<unsigned int,
          std::pair<std::shared_ptr<ConstructorBugs::state>, unsigned int>>
ConstructorBugs::pair_test(const unsigned int n) {
  std::shared_ptr<ConstructorBugs::state> s = get_state(n);
  return std::make_pair(n, std::make_pair(s, s->value));
}

__attribute__((pure))
std::optional<std::pair<std::shared_ptr<ConstructorBugs::state>, unsigned int>>
ConstructorBugs::match_test(
    const std::optional<std::shared_ptr<ConstructorBugs::state>> o) {
  if (o.has_value()) {
    std::shared_ptr<ConstructorBugs::state> s = *o;
    return std::make_optional<
        std::pair<std::shared_ptr<ConstructorBugs::state>, unsigned int>>(
        std::make_pair(s, s->value));
  } else {
    return std::optional<
        std::pair<std::shared_ptr<ConstructorBugs::state>, unsigned int>>();
  }
}

std::shared_ptr<List<std::shared_ptr<ConstructorBugs::state>>>
ConstructorBugs::list_test(std::shared_ptr<ConstructorBugs::state> s) {
  return List<std::shared_ptr<ConstructorBugs::state>>::cons(
      s, List<std::shared_ptr<ConstructorBugs::state>>::cons(
             s, List<std::shared_ptr<ConstructorBugs::state>>::cons(
                    s, List<std::shared_ptr<ConstructorBugs::state>>::nil())));
}

__attribute__((pure)) std::pair<
    std::pair<std::pair<std::shared_ptr<ConstructorBugs::state>, unsigned int>,
              std::pair<unsigned int, std::shared_ptr<List<unsigned int>>>>,
    std::shared_ptr<List<unsigned int>>>
ConstructorBugs::triple_proj(std::shared_ptr<ConstructorBugs::state> s) {
  return std::make_pair(std::make_pair(std::make_pair(s, s->value),
                                       std::make_pair(s->value, s->data)),
                        s->data);
}

__attribute__((pure))
std::pair<std::shared_ptr<ConstructorBugs::state>, unsigned int>
ConstructorBugs::inner_pair(std::shared_ptr<ConstructorBugs::state> s) {
  return std::make_pair(s, s->value);
}

__attribute__((pure))
std::pair<std::shared_ptr<ConstructorBugs::state>, unsigned int>
ConstructorBugs::outer_call(const unsigned int n) {
  return inner_pair(get_state(n));
}

__attribute__((pure)) std::pair<
    std::pair<std::pair<std::pair<std::shared_ptr<ConstructorBugs::state>,
                                  std::shared_ptr<ConstructorBugs::state>>,
                        unsigned int>,
              unsigned int>,
    std::shared_ptr<List<unsigned int>>>
ConstructorBugs::extreme_reuse(std::shared_ptr<ConstructorBugs::state> s) {
  return std::make_pair(
      std::make_pair(std::make_pair(std::make_pair(s, s), s->value), s->value),
      s->data);
}

std::shared_ptr<ConstructorBugs::Outer>
ConstructorBugs::nested_record(std::shared_ptr<ConstructorBugs::Inner> i) {
  return std::make_shared<ConstructorBugs::Outer>(Outer{i, i->inner_val});
}

std::shared_ptr<ConstructorBugs::Outer> ConstructorBugs::self_referential(
    const std::shared_ptr<ConstructorBugs::Outer> &o) {
  return std::make_shared<ConstructorBugs::Outer>(
      Outer{o->outer_inner, o->outer_inner->inner_val});
}

__attribute__((pure))
std::pair<std::shared_ptr<ConstructorBugs::Inner>, unsigned int>
ConstructorBugs::pair_with_proj(std::shared_ptr<ConstructorBugs::Inner> i) {
  return std::make_pair(i, i->inner_val);
}

__attribute__((pure))
std::pair<std::pair<std::shared_ptr<ConstructorBugs::Inner>, unsigned int>,
          std::pair<unsigned int, unsigned int>>
ConstructorBugs::nested_pairs(std::shared_ptr<ConstructorBugs::Inner> i) {
  return std::make_pair(std::make_pair(i, i->inner_val),
                        std::make_pair(i->inner_val, i->inner_val));
}

__attribute__((pure)) std::pair<std::shared_ptr<ConstructorBugs::Inner>,
                                std::shared_ptr<ConstructorBugs::Inner>>
ConstructorBugs::pair_duplicate(std::shared_ptr<ConstructorBugs::Inner> i) {
  return std::make_pair(i, i);
}

std::shared_ptr<ConstructorBugs::Inner>
ConstructorBugs::mk_inner(const unsigned int n) {
  return std::make_shared<ConstructorBugs::Inner>(Inner{n});
}

__attribute__((pure))
std::pair<std::shared_ptr<ConstructorBugs::Inner>, unsigned int>
ConstructorBugs::pair_from_func(const unsigned int n) {
  std::shared_ptr<ConstructorBugs::Inner> i = mk_inner(n);
  return std::make_pair(i, i->inner_val);
}

__attribute__((pure))
std::optional<std::pair<std::shared_ptr<ConstructorBugs::Inner>, unsigned int>>
ConstructorBugs::match_option_record(
    const std::optional<std::shared_ptr<ConstructorBugs::Inner>> o) {
  if (o.has_value()) {
    std::shared_ptr<ConstructorBugs::Inner> i = *o;
    return std::make_optional<
        std::pair<std::shared_ptr<ConstructorBugs::Inner>, unsigned int>>(
        std::make_pair(i, i->inner_val));
  } else {
    return std::optional<
        std::pair<std::shared_ptr<ConstructorBugs::Inner>, unsigned int>>();
  }
}

__attribute__((pure))
std::pair<std::shared_ptr<ConstructorBugs::Inner>, unsigned int>
ConstructorBugs::match_sum(const std::shared_ptr<ConstructorBugs::MySum> &s) {
  return std::visit(
      Overloaded{[](const typename ConstructorBugs::MySum::Left &_args)
                     -> std::pair<std::shared_ptr<ConstructorBugs::Inner>,
                                  unsigned int> {
                   return std::make_pair(_args.d_a0, _args.d_a0->inner_val);
                 },
                 [](const typename ConstructorBugs::MySum::Right &_args)
                     -> std::pair<std::shared_ptr<ConstructorBugs::Inner>,
                                  unsigned int> {
                   return std::make_pair(
                       std::make_shared<ConstructorBugs::Inner>(
                           Inner{_args.d_a0}),
                       _args.d_a0);
                 }},
      s->v());
}

__attribute__((pure))
std::pair<std::shared_ptr<ConstructorBugs::Inner>, unsigned int>
ConstructorBugs::with_cast(std::shared_ptr<ConstructorBugs::Inner> i) {
  return std::make_pair(i, i->inner_val);
}

__attribute__((pure))
std::pair<std::pair<std::shared_ptr<ConstructorBugs::Inner>, unsigned int>,
          std::pair<std::shared_ptr<ConstructorBugs::Inner>, unsigned int>>
ConstructorBugs::chain_lets(const std::shared_ptr<ConstructorBugs::Inner> &i1) {
  std::shared_ptr<ConstructorBugs::Inner> i2 =
      std::make_shared<ConstructorBugs::Inner>(Inner{i1->inner_val});
  std::shared_ptr<ConstructorBugs::Inner> i3 =
      std::make_shared<ConstructorBugs::Inner>(Inner{i2->inner_val});
  return std::make_pair(std::make_pair(i2, i2->inner_val),
                        std::make_pair(i3, i3->inner_val));
}

__attribute__((pure))
std::pair<std::pair<std::shared_ptr<ConstructorBugs::Outer>,
                    std::shared_ptr<ConstructorBugs::Inner>>,
          unsigned int>
ConstructorBugs::deep_proj(
    const std::shared_ptr<ConstructorBugs::Container> &c) {
  std::shared_ptr<ConstructorBugs::Outer> o = c->cont_outer;
  std::shared_ptr<ConstructorBugs::Inner> i = o->outer_inner;
  return std::make_pair(std::make_pair(o, i), i->inner_val);
}

__attribute__((pure))
std::pair<std::shared_ptr<List<std::shared_ptr<ConstructorBugs::Inner>>>,
          unsigned int>
ConstructorBugs::list_with_proj(std::shared_ptr<ConstructorBugs::Inner> i) {
  return std::make_pair(
      List<std::shared_ptr<ConstructorBugs::Inner>>::cons(
          i,
          List<std::shared_ptr<ConstructorBugs::Inner>>::cons(
              i, List<std::shared_ptr<ConstructorBugs::Inner>>::cons(
                     i, List<std::shared_ptr<ConstructorBugs::Inner>>::nil()))),
      i->inner_val);
}

__attribute__((pure))
std::pair<std::shared_ptr<ConstructorBugs::Inner>, unsigned int>
ConstructorBugs::tail_pair(std::shared_ptr<ConstructorBugs::Inner> i,
                           const bool b) {
  if (b) {
    return std::make_pair(i, i->inner_val);
  } else {
    return std::make_pair(i, 0u);
  }
}

__attribute__((pure))
std::pair<std::pair<std::shared_ptr<ConstructorBugs::Inner>,
                    std::shared_ptr<ConstructorBugs::Inner>>,
          std::pair<unsigned int, unsigned int>>
ConstructorBugs::quad_tuple(std::shared_ptr<ConstructorBugs::Inner> i) {
  return std::make_pair(std::make_pair(i, i),
                        std::make_pair(i->inner_val, i->inner_val));
}

__attribute__((pure))
std::pair<std::optional<std::shared_ptr<ConstructorBugs::Inner>>, unsigned int>
ConstructorBugs::match_both_branches(
    const std::optional<std::shared_ptr<ConstructorBugs::Inner>> o) {
  if (o.has_value()) {
    std::shared_ptr<ConstructorBugs::Inner> i = *o;
    return std::make_pair(
        std::make_optional<std::shared_ptr<ConstructorBugs::Inner>>(i),
        i->inner_val);
  } else {
    return std::make_pair(
        std::optional<std::shared_ptr<ConstructorBugs::Inner>>(), 0u);
  }
}

std::shared_ptr<Sig<std::shared_ptr<ConstructorBugs::Inner>>>
ConstructorBugs::sigma_test(std::shared_ptr<ConstructorBugs::Inner> i) {
  return Sig<std::shared_ptr<ConstructorBugs::Inner>>::exist(i);
}

__attribute__((pure)) unsigned int
ConstructorBugs::extract(const std::shared_ptr<ConstructorBugs::Inner> &i) {
  return i->inner_val;
}

__attribute__((pure))
std::pair<std::shared_ptr<ConstructorBugs::Inner>, unsigned int>
ConstructorBugs::nested_extract(std::shared_ptr<ConstructorBugs::Inner> i) {
  return std::make_pair(i, extract(i));
}

__attribute__((pure))
std::pair<std::shared_ptr<ConstructorBugs::Outer>, unsigned int>
ConstructorBugs::update_test(const std::shared_ptr<ConstructorBugs::Outer> &o) {
  return std::make_pair(std::make_shared<ConstructorBugs::Outer>(
                            Outer{o->outer_inner, (o->outer_data + 1u)}),
                        o->outer_inner->inner_val);
}

__attribute__((pure))
std::pair<std::shared_ptr<ConstructorBugs::State>, unsigned int>
ConstructorBugs::inline_pair(std::shared_ptr<ConstructorBugs::State> s) {
  return std::make_pair(s, s->value_inline);
}

__attribute__((pure))
std::pair<std::pair<std::shared_ptr<ConstructorBugs::State>, unsigned int>,
          unsigned int>
ConstructorBugs::inline_triple(std::shared_ptr<ConstructorBugs::State> s) {
  return std::make_pair(std::make_pair(s, s->value_inline), s->data_inline);
}

__attribute__((pure))
std::pair<std::pair<std::shared_ptr<ConstructorBugs::State>, unsigned int>,
          unsigned int>
ConstructorBugs::inline_nested(std::shared_ptr<ConstructorBugs::State> s) {
  return std::make_pair(std::make_pair(s, s->value_inline), s->data_inline);
}

std::shared_ptr<ConstructorBugs::State>
ConstructorBugs::get_state_inline(const unsigned int n) {
  return std::make_shared<ConstructorBugs::State>(State{n, n, n});
}

__attribute__((pure))
std::pair<std::shared_ptr<ConstructorBugs::State>, unsigned int>
ConstructorBugs::inline_from_call(const unsigned int n) {
  return std::make_pair(get_state_inline(n), get_state_inline(n)->value_inline);
}

__attribute__((pure))
std::pair<std::pair<std::shared_ptr<ConstructorBugs::State>, unsigned int>,
          unsigned int>
ConstructorBugs::same_call_multi_proj(const unsigned int n) {
  return std::make_pair(
      std::make_pair(get_state_inline(n), get_state_inline(n)->value_inline),
      get_state_inline(n)->data_inline);
}

__attribute__((pure))
std::optional<std::pair<std::shared_ptr<ConstructorBugs::State>, unsigned int>>
ConstructorBugs::inline_match(
    const std::optional<std::shared_ptr<ConstructorBugs::State>> o) {
  if (o.has_value()) {
    std::shared_ptr<ConstructorBugs::State> s = *o;
    return std::make_optional<
        std::pair<std::shared_ptr<ConstructorBugs::State>, unsigned int>>(
        std::make_pair(s, s->value_inline));
  } else {
    return std::optional<
        std::pair<std::shared_ptr<ConstructorBugs::State>, unsigned int>>();
  }
}

__attribute__((pure))
std::pair<std::shared_ptr<ConstructorBugs::State>, unsigned int>
ConstructorBugs::inline_if(const bool b,
                           std::shared_ptr<ConstructorBugs::State> s) {
  if (b) {
    return std::make_pair(s, s->value_inline);
  } else {
    return std::make_pair(s, 0u);
  }
}

__attribute__((pure))
std::pair<std::pair<std::shared_ptr<ConstructorBugs::OuterInline>,
                    std::shared_ptr<ConstructorBugs::State>>,
          unsigned int>
ConstructorBugs::inline_deep(std::shared_ptr<ConstructorBugs::OuterInline> o) {
  return std::make_pair(std::make_pair(o, o->outer_state),
                        o->outer_state->value_inline);
}

__attribute__((pure))
std::pair<std::shared_ptr<ConstructorBugs::State>, unsigned int>
ConstructorBugs::inline_double_proj(
    const std::shared_ptr<ConstructorBugs::OuterInline> &o) {
  return std::make_pair(o->outer_state, o->outer_state->value_inline);
}

__attribute__((pure))
std::pair<std::pair<std::shared_ptr<ConstructorBugs::State>, unsigned int>,
          std::pair<unsigned int, unsigned int>>
ConstructorBugs::inline_many(std::shared_ptr<ConstructorBugs::State> s) {
  return std::make_pair(std::make_pair(s, s->value_inline),
                        std::make_pair(s->data_inline, s->flag));
}

__attribute__((pure))
std::pair<std::pair<unsigned int, std::shared_ptr<ConstructorBugs::State>>,
          unsigned int>
ConstructorBugs::inline_pattern(std::shared_ptr<ConstructorBugs::State> s) {
  unsigned int v = s->value_inline;
  unsigned int d = s->data_inline;
  std::any _x = s->flag;
  return std::make_pair(std::make_pair(v, s), d);
}

std::shared_ptr<
    List<std::pair<std::shared_ptr<ConstructorBugs::State>, unsigned int>>>
ConstructorBugs::inline_recursive(const unsigned int n,
                                  std::shared_ptr<ConstructorBugs::State> s) {
  if (n <= 0) {
    return List<std::pair<std::shared_ptr<ConstructorBugs::State>,
                          unsigned int>>::nil();
  } else {
    unsigned int m = n - 1;
    return List<std::pair<std::shared_ptr<ConstructorBugs::State>,
                          unsigned int>>::cons(std::make_pair(s,
                                                              s->value_inline),
                                               inline_recursive(m, s));
  }
}

__attribute__((pure)) std::pair<
    std::pair<std::pair<std::shared_ptr<ConstructorBugs::State>, unsigned int>,
              unsigned int>,
    std::pair<unsigned int, std::shared_ptr<ConstructorBugs::State>>>
ConstructorBugs::inline_complex(std::shared_ptr<ConstructorBugs::State> s) {
  return std::make_pair(
      std::make_pair(std::make_pair(s, s->value_inline), s->data_inline),
      std::make_pair(s->flag, s));
}

__attribute__((pure))
std::pair<std::pair<std::shared_ptr<ConstructorBugs::State>,
                    std::shared_ptr<ConstructorBugs::State>>,
          std::pair<unsigned int, unsigned int>>
ConstructorBugs::inline_quad(std::shared_ptr<ConstructorBugs::State> s) {
  return std::make_pair(std::make_pair(s, s),
                        std::make_pair(s->value_inline, s->data_inline));
}

__attribute__((pure))
std::pair<std::shared_ptr<ConstructorBugs::State>, unsigned int>
ConstructorBugs::inline_both_branches(
    const bool b, std::shared_ptr<ConstructorBugs::State> s) {
  if (b) {
    return std::make_pair(s, s->value_inline);
  } else {
    return std::make_pair(s, s->value_inline);
  }
}

__attribute__((pure))
std::pair<std::pair<std::shared_ptr<ConstructorBugs::State>, unsigned int>,
          unsigned int>
ConstructorBugs::test_apply(const std::shared_ptr<ConstructorBugs::State> &s) {
  return apply_twice(
      [](std::shared_ptr<ConstructorBugs::State> s0) {
        return s0->value_inline;
      },
      s);
}

__attribute__((pure)) unsigned int ConstructorBugs::get_value_inline(
    const std::shared_ptr<ConstructorBugs::State> &s) {
  return s->value_inline;
}

__attribute__((pure)) unsigned int ConstructorBugs::get_data_inline(
    const std::shared_ptr<ConstructorBugs::State> &s) {
  return s->data_inline;
}

__attribute__((pure))
std::pair<std::pair<std::shared_ptr<ConstructorBugs::State>, unsigned int>,
          unsigned int>
ConstructorBugs::inline_nested_calls(
    std::shared_ptr<ConstructorBugs::State> s) {
  return std::make_pair(std::make_pair(s, get_value_inline(s)),
                        get_data_inline(s));
}

__attribute__((pure))
std::pair<std::optional<std::shared_ptr<ConstructorBugs::State>>,
          std::optional<unsigned int>>
ConstructorBugs::inline_option(std::shared_ptr<ConstructorBugs::State> s) {
  return std::make_pair(
      std::make_optional<std::shared_ptr<ConstructorBugs::State>>(s),
      std::make_optional<unsigned int>(s->value_inline));
}

__attribute__((pure))
std::pair<std::shared_ptr<List<std::shared_ptr<ConstructorBugs::State>>>,
          std::shared_ptr<List<unsigned int>>>
ConstructorBugs::inline_list(std::shared_ptr<ConstructorBugs::State> s) {
  return std::make_pair(
      List<std::shared_ptr<ConstructorBugs::State>>::cons(
          s, List<std::shared_ptr<ConstructorBugs::State>>::nil()),
      List<unsigned int>::cons(s->value_inline, List<unsigned int>::nil()));
}
