#include "comprehensive_patterns.h"

std::pair<std::pair<ComprehensivePatterns::S, uint64_t>, uint64_t>
ComprehensivePatterns::syntactic_variation(ComprehensivePatterns::S s) {
  uint64_t a = s.s_a;
  std::function<uint64_t(ComprehensivePatterns::S)> b =
      [](const ComprehensivePatterns::S &s0) { return s0.s_b; };
  return std::make_pair(std::make_pair(s, a), b(s));
}

std::pair<ComprehensivePatterns::S, uint64_t>
ComprehensivePatterns::with_magic(ComprehensivePatterns::S s) {
  return std::make_pair(s, s.s_a);
}

std::pair<
    std::pair<
        std::pair<std::pair<std::pair<std::pair<ComprehensivePatterns::L5,
                                                ComprehensivePatterns::L4>,
                                      ComprehensivePatterns::L3>,
                            ComprehensivePatterns::L2>,
                  ComprehensivePatterns::L1>,
        ComprehensivePatterns::S>,
    uint64_t>
ComprehensivePatterns::deep_nest(ComprehensivePatterns::L5 l5) {
  const ComprehensivePatterns::L4 &l4 = l5.l5_l4;
  const ComprehensivePatterns::L3 &l3 = l4.l4_l3;
  const ComprehensivePatterns::L2 &l2 = l3.l3_l2;
  const ComprehensivePatterns::L1 &l1 = l2.l2_l1;
  const ComprehensivePatterns::S &s = l1.l1_s;
  return std::make_pair(
      std::make_pair(
          std::make_pair(
              std::make_pair(
                  std::make_pair(std::make_pair(std::move(l5), l4), l3), l2),
              l1),
          s),
      s.s_a);
}

std::pair<std::pair<std::pair<ComprehensivePatterns::S, uint64_t>, uint64_t>,
          uint64_t>
ComprehensivePatterns::nested_pair_reuse(ComprehensivePatterns::S s) {
  return std::make_pair(std::make_pair(std::make_pair(s, s.s_a), s.s_b), s.s_c);
}

std::pair<ComprehensivePatterns::S, uint64_t>
ComprehensivePatterns::compose(ComprehensivePatterns::S s) {
  std::function<uint64_t(ComprehensivePatterns::S)> f =
      [](const ComprehensivePatterns::S &x) { return x.s_a; };
  return std::make_pair(s, f(s));
}

std::pair<std::function<uint64_t(uint64_t)>, ComprehensivePatterns::S>
ComprehensivePatterns::lambda_proj(ComprehensivePatterns::S s) {
  return std::make_pair([=](uint64_t) mutable { return s.s_a; }, s);
}

std::pair<std::pair<std::pair<ComprehensivePatterns::S, uint64_t>, uint64_t>,
          uint64_t>
ComprehensivePatterns::proj_chain(ComprehensivePatterns::S s) {
  uint64_t a = s.s_a;
  uint64_t b = s.s_b;
  uint64_t c = s.s_c;
  return std::make_pair(std::make_pair(std::make_pair(std::move(s), a), b), c);
}

std::pair<
    std::pair<std::pair<ComprehensivePatterns::S, ComprehensivePatterns::S>,
              std::pair<uint64_t, uint64_t>>,
    std::pair<std::pair<uint64_t, uint64_t>, std::pair<uint64_t, uint64_t>>>
ComprehensivePatterns::octuple(ComprehensivePatterns::S s) {
  return std::make_pair(
      std::make_pair(std::make_pair(s, s), std::make_pair(s.s_a, s.s_b)),
      std::make_pair(std::make_pair(s.s_c, s.s_a),
                     std::make_pair(s.s_b, s.s_c)));
}

std::pair<std::optional<std::pair<ComprehensivePatterns::S, uint64_t>>,
          ComprehensivePatterns::S>
ComprehensivePatterns::nested_containers(ComprehensivePatterns::S s) {
  return std::make_pair(
      std::make_optional<std::pair<ComprehensivePatterns::S, uint64_t>>(
          std::make_pair(s, s.s_a)),
      s);
}

std::pair<std::pair<ComprehensivePatterns::S, uint64_t>, uint64_t>
ComprehensivePatterns::match_pair(
    const std::pair<ComprehensivePatterns::S, uint64_t> &p) {
  const ComprehensivePatterns::S &s = p.first;
  const uint64_t &n = p.second;
  return std::make_pair(std::make_pair(s, n), s.s_a);
}

List<std::pair<ComprehensivePatterns::S, uint64_t>>
ComprehensivePatterns::make_list(uint64_t n, ComprehensivePatterns::S s) {
  std::unique_ptr<List<std::pair<ComprehensivePatterns::S, uint64_t>>> _head{};
  std::unique_ptr<List<std::pair<ComprehensivePatterns::S, uint64_t>>> *_write =
      &_head;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      *_write =
          std::make_unique<List<std::pair<ComprehensivePatterns::S, uint64_t>>>(
              List<std::pair<ComprehensivePatterns::S, uint64_t>>::nil());
      break;
    } else {
      uint64_t m = _loop_n - 1;
      auto _cell = std::make_unique<
          List<std::pair<ComprehensivePatterns::S, uint64_t>>>(
          typename List<std::pair<ComprehensivePatterns::S, uint64_t>>::Cons(
              std::make_pair(s, s.s_a), nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename List<
          std::pair<ComprehensivePatterns::S, uint64_t>>::Cons>(
                    (*_write)->v_mut())
                    .l;
      _loop_n = m;
      continue;
    }
  }
  return std::move(*_head);
}

std::optional<std::pair<ComprehensivePatterns::S, ComprehensivePatterns::S>>
ComprehensivePatterns::multi_match(
    const std::optional<ComprehensivePatterns::S> &o1,
    const std::optional<ComprehensivePatterns::S> &o2) {
  if (o1.has_value()) {
    const ComprehensivePatterns::S &s1 = *o1;
    if (o2.has_value()) {
      const ComprehensivePatterns::S &_x = *o2;
      return std::make_optional<
          std::pair<ComprehensivePatterns::S, ComprehensivePatterns::S>>(
          std::make_pair(s1, s1));
    } else {
      return std::make_optional<
          std::pair<ComprehensivePatterns::S, ComprehensivePatterns::S>>(
          std::make_pair(s1, s1));
    }
  } else {
    return std::optional<
        std::pair<ComprehensivePatterns::S, ComprehensivePatterns::S>>();
  }
}

std::pair<ComprehensivePatterns::S, uint64_t>
ComprehensivePatterns::match_three(ComprehensivePatterns::Three t,
                                   ComprehensivePatterns::S s) {
  switch (t) {
  case Three::A: {
    return std::make_pair(s, s.s_a);
  }
  case Three::B: {
    return std::make_pair(s, s.s_b);
  }
  case Three::C: {
    return std::make_pair(s, s.s_c);
  }
  default:
    std::unreachable();
  }
}

std::pair<ComprehensivePatterns::S, uint64_t>
ComprehensivePatterns::let_in_arg(ComprehensivePatterns::S s) {
  return std::make_pair(s, s.s_a);
}

std::pair<ComprehensivePatterns::S, uint64_t>
ComprehensivePatterns::match_record(ComprehensivePatterns::S s) {
  uint64_t a = s.s_a;
  std::any _x = s.s_b;
  std::any _x0 = s.s_c;
  return std::make_pair(std::move(s), a);
}

std::pair<ComprehensivePatterns::S, uint64_t>
ComprehensivePatterns::rebind(ComprehensivePatterns::S s1) {
  return std::make_pair(s1, s1.s_a);
}

std::pair<std::function<uint64_t(std::monostate)>,
          std::function<uint64_t(std::monostate)>>
ComprehensivePatterns::closure_pair(ComprehensivePatterns::S s) {
  return std::make_pair([=](std::monostate) mutable { return s.s_a; },
                        [=](std::monostate) mutable { return s.s_b; });
}

Sig<ComprehensivePatterns::S>
ComprehensivePatterns::sigma_reuse(ComprehensivePatterns::S s) {
  return Sig<ComprehensivePatterns::S>::exist(std::move(s));
}

std::pair<uint64_t, std::pair<uint64_t, uint64_t>>
ComprehensivePatterns::multi_proj_arg(const ComprehensivePatterns::S &s) {
  return std::make_pair(s.s_a, std::make_pair(s.s_a, s.s_b));
}

std::pair<ComprehensivePatterns::Either, ComprehensivePatterns::Either>
ComprehensivePatterns::both_in_sum(ComprehensivePatterns::S s) {
  return std::make_pair(Either::left_s(s), Either::right_n(s.s_a));
}

std::pair<
    std::pair<std::pair<ComprehensivePatterns::R3, ComprehensivePatterns::R2>,
              ComprehensivePatterns::R1>,
    uint64_t>
ComprehensivePatterns::hard_proj_chain(ComprehensivePatterns::R3 r3) {
  const ComprehensivePatterns::R2 &r2 = r3.r3_r2;
  const ComprehensivePatterns::R1 &r1 = r2.r2_inner;
  return std::make_pair(std::make_pair(std::make_pair(std::move(r3), r2), r1),
                        r1.r1_val);
}

std::pair<std::pair<ComprehensivePatterns::R2, ComprehensivePatterns::R1>,
          uint64_t>
ComprehensivePatterns::multi_path(const ComprehensivePatterns::R3 &r3) {
  return std::make_pair(std::make_pair(r3.r3_r2, r3.r3_r2.r2_inner),
                        r3.r3_r2.r2_inner.r1_val);
}

std::pair<std::pair<ComprehensivePatterns::R2, ComprehensivePatterns::R1>,
          uint64_t>
ComprehensivePatterns::let_proj(ComprehensivePatterns::R2 r2) {
  const ComprehensivePatterns::R1 &r1 = r2.r2_inner;
  uint64_t n = r1.r1_val;
  return std::make_pair(std::make_pair(std::move(r2), r1), n);
}

uint64_t
ComprehensivePatterns::extract_val(const ComprehensivePatterns::R1 &r1) {
  return r1.r1_val;
}

std::pair<ComprehensivePatterns::R2, uint64_t>
ComprehensivePatterns::nested_call(ComprehensivePatterns::R2 r2) {
  return std::make_pair(r2, extract_val(r2.r2_inner));
}

std::pair<std::pair<ComprehensivePatterns::R2, ComprehensivePatterns::R1>,
          uint64_t>
ComprehensivePatterns::multi_proj_let(uint64_t n) {
  ComprehensivePatterns::R2 r2 = R2{R1{n}, n};
  return std::make_pair(std::make_pair(r2, r2.r2_inner), r2.r2_data);
}

std::optional<std::pair<ComprehensivePatterns::R2, ComprehensivePatterns::R1>>
ComprehensivePatterns::match_proj(ComprehensivePatterns::R2 r2) {
  const ComprehensivePatterns::R1 &r1 = r2.r2_inner;
  return std::make_optional<
      std::pair<ComprehensivePatterns::R2, ComprehensivePatterns::R1>>(
      std::make_pair(std::move(r2), r1));
}

std::pair<std::pair<ComprehensivePatterns::R1, uint64_t>, uint64_t>
ComprehensivePatterns::proj_multi_use(const ComprehensivePatterns::R2 &r2) {
  const ComprehensivePatterns::R1 &r1 = r2.r2_inner;
  return std::make_pair(std::make_pair(r1, r1.r1_val), r1.r1_val);
}

std::pair<std::pair<ComprehensivePatterns::R3, ComprehensivePatterns::R2>,
          std::pair<ComprehensivePatterns::R1, uint64_t>>
ComprehensivePatterns::complex_nest(ComprehensivePatterns::R3 r3) {
  return std::make_pair(
      std::make_pair(r3, r3.r3_r2),
      std::make_pair(r3.r3_r2.r2_inner, r3.r3_r2.r2_inner.r1_val));
}

ComprehensivePatterns::R2 ComprehensivePatterns::make_r2(uint64_t n) {
  return R2{R1{n}, n};
}

std::pair<std::pair<ComprehensivePatterns::R2, ComprehensivePatterns::R1>,
          uint64_t>
ComprehensivePatterns::from_func(uint64_t n) {
  ComprehensivePatterns::R2 r2 = make_r2(n);
  return std::make_pair(std::make_pair(r2, r2.r2_inner), r2.r2_data);
}

std::pair<std::pair<ComprehensivePatterns::R2, ComprehensivePatterns::R1>,
          std::pair<ComprehensivePatterns::R1, uint64_t>>
ComprehensivePatterns::pair_of_pairs(ComprehensivePatterns::R2 r2) {
  const ComprehensivePatterns::R1 &r1 = r2.r2_inner;
  return std::make_pair(std::make_pair(std::move(r2), r1),
                        std::make_pair(r1, r1.r1_val));
}

std::pair<ComprehensivePatterns::R2, ComprehensivePatterns::R1>
ComprehensivePatterns::cond_proj(bool b, ComprehensivePatterns::R2 r2) {
  if (b) {
    return std::make_pair(r2, r2.r2_inner);
  } else {
    return std::make_pair(r2, r2.r2_inner);
  }
}

List<std::pair<ComprehensivePatterns::R2, ComprehensivePatterns::R1>>
ComprehensivePatterns::repeat_r2(uint64_t n, ComprehensivePatterns::R2 r2) {
  std::unique_ptr<
      List<std::pair<ComprehensivePatterns::R2, ComprehensivePatterns::R1>>>
      _head{};
  std::unique_ptr<
      List<std::pair<ComprehensivePatterns::R2, ComprehensivePatterns::R1>>>
      *_write = &_head;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      *_write = std::make_unique<List<
          std::pair<ComprehensivePatterns::R2, ComprehensivePatterns::R1>>>(
          List<std::pair<ComprehensivePatterns::R2,
                         ComprehensivePatterns::R1>>::nil());
      break;
    } else {
      uint64_t m = _loop_n - 1;
      auto _cell = std::make_unique<List<
          std::pair<ComprehensivePatterns::R2, ComprehensivePatterns::R1>>>(
          typename List<
              std::pair<ComprehensivePatterns::R2, ComprehensivePatterns::R1>>::
              Cons(std::make_pair(r2, r2.r2_inner), nullptr));
      *_write = std::move(_cell);
      _write =
          &std::get<typename List<std::pair<ComprehensivePatterns::R2,
                                            ComprehensivePatterns::R1>>::Cons>(
               (*_write)->v_mut())
               .l;
      _loop_n = m;
      continue;
    }
  }
  return std::move(*_head);
}

std::pair<std::pair<ComprehensivePatterns::R3, ComprehensivePatterns::R2>,
          ComprehensivePatterns::R1>
ComprehensivePatterns::nested_lets(ComprehensivePatterns::R3 r3) {
  const ComprehensivePatterns::R2 &r2 = r3.r3_r2;
  const ComprehensivePatterns::R1 &r1 = r2.r2_inner;
  return std::make_pair(std::make_pair(std::move(r3), r2), r1);
}

std::pair<ComprehensivePatterns::R1, uint64_t>
ComprehensivePatterns::double_proj(const ComprehensivePatterns::R3 &r3) {
  return std::make_pair(r3.r3_r2.r2_inner, r3.r3_r2.r2_inner.r1_val);
}

std::pair<std::pair<ComprehensivePatterns::R3, ComprehensivePatterns::R2>,
          ComprehensivePatterns::R2>
ComprehensivePatterns::mixed_access(ComprehensivePatterns::R3 r3) {
  const ComprehensivePatterns::R2 &r2 = r3.r3_r2;
  return std::make_pair(std::make_pair(r3, r2), r3.r3_r2);
}

std::pair<ComprehensivePatterns::R2, ComprehensivePatterns::R1>
ComprehensivePatterns::return_proj_h(ComprehensivePatterns::R2 r2) {
  return std::make_pair(r2, r2.r2_inner);
}

std::pair<
    std::pair<std::pair<ComprehensivePatterns::R3, ComprehensivePatterns::R2>,
              ComprehensivePatterns::R1>,
    uint64_t>
ComprehensivePatterns::all_levels(ComprehensivePatterns::R3 r3) {
  return std::make_pair(
      std::make_pair(std::make_pair(r3, r3.r3_r2), r3.r3_r2.r2_inner),
      r3.r3_r2.r2_inner.r1_val);
}

std::pair<ComprehensivePatterns::R1, ComprehensivePatterns::R1>
ComprehensivePatterns::let_and_proj(const ComprehensivePatterns::R2 &r2) {
  const ComprehensivePatterns::R1 &r1 = r2.r2_inner;
  return std::make_pair(r1, r2.r2_inner);
}

std::pair<ComprehensivePatterns::R2, ComprehensivePatterns::R2>
ComprehensivePatterns::multi_construct(ComprehensivePatterns::R1 r1) {
  ComprehensivePatterns::R2 r2a = R2{r1, UINT64_C(0)};
  ComprehensivePatterns::R2 r2b = R2{r1, UINT64_C(1)};
  return std::make_pair(std::move(r2a), std::move(r2b));
}

std::optional<std::pair<ComprehensivePatterns::R2, ComprehensivePatterns::R1>>
ComprehensivePatterns::option_proj(
    const std::optional<ComprehensivePatterns::R2> &o) {
  if (o.has_value()) {
    const ComprehensivePatterns::R2 &r2 = *o;
    return std::make_optional<
        std::pair<ComprehensivePatterns::R2, ComprehensivePatterns::R1>>(
        std::make_pair(r2, r2.r2_inner));
  } else {
    return std::optional<
        std::pair<ComprehensivePatterns::R2, ComprehensivePatterns::R1>>();
  }
}

std::pair<ComprehensivePatterns::R, uint64_t>
ComprehensivePatterns::pair_inline_proj(ComprehensivePatterns::R r) {
  return std::make_pair(r, r.val);
}

std::pair<std::pair<ComprehensivePatterns::R, uint64_t>, uint64_t>
ComprehensivePatterns::nested_pair_inline(ComprehensivePatterns::R r) {
  return std::make_pair(std::make_pair(r, r.val), r.dat);
}

uint64_t
ComprehensivePatterns::match_bind_and_use(const ComprehensivePatterns::R &r) {
  uint64_t v = r.val;
  uint64_t d = r.dat;
  return ((v + d) + r.val);
}

uint64_t
ComprehensivePatterns::let_with_type(const ComprehensivePatterns::R &r) {
  return (r.val + r.val);
}

uint64_t
ComprehensivePatterns::proj_of_last_use(const ComprehensivePatterns::R &r1) {
  return r1.val;
}

uint64_t
ComprehensivePatterns::multi_let_same(const ComprehensivePatterns::R &r) {
  return ((r.val + r.val) + r.val);
}

uint64_t ComprehensivePatterns::option_unwrap_proj(
    const std::optional<ComprehensivePatterns::R> &o) {
  if (o.has_value()) {
    const ComprehensivePatterns::R &r = *o;
    return (r.val + r.dat);
  } else {
    return UINT64_C(0);
  }
}

std::pair<ComprehensivePatterns::R, uint64_t>
ComprehensivePatterns::fun_result_and_proj(uint64_t n) {
  ComprehensivePatterns::R r = R{n, n};
  return std::make_pair(r, r.val);
}

std::optional<uint64_t> ComprehensivePatterns::match_multi_use(
    const std::optional<ComprehensivePatterns::R> &o) {
  if (o.has_value()) {
    const ComprehensivePatterns::R &r = *o;
    return std::make_optional<uint64_t>((r.val + r.dat));
  } else {
    return std::optional<uint64_t>();
  }
}

std::pair<std::pair<ComprehensivePatterns::R, uint64_t>, uint64_t>
ComprehensivePatterns::tuple_proj(ComprehensivePatterns::R r) {
  return std::make_pair(std::make_pair(r, r.val), r.dat);
}

std::pair<ComprehensivePatterns::R, uint64_t>
ComprehensivePatterns::chain_to_pair(ComprehensivePatterns::R r1) {
  return std::make_pair(r1, r1.val);
}

List<std::pair<ComprehensivePatterns::R, uint64_t>>
ComprehensivePatterns::repeat_pair(uint64_t n, ComprehensivePatterns::R r) {
  std::unique_ptr<List<std::pair<ComprehensivePatterns::R, uint64_t>>> _head{};
  std::unique_ptr<List<std::pair<ComprehensivePatterns::R, uint64_t>>> *_write =
      &_head;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      *_write =
          std::make_unique<List<std::pair<ComprehensivePatterns::R, uint64_t>>>(
              List<std::pair<ComprehensivePatterns::R, uint64_t>>::nil());
      break;
    } else {
      uint64_t m = _loop_n - 1;
      auto _cell = std::make_unique<
          List<std::pair<ComprehensivePatterns::R, uint64_t>>>(
          typename List<std::pair<ComprehensivePatterns::R, uint64_t>>::Cons(
              std::make_pair(r, r.val), nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename List<
          std::pair<ComprehensivePatterns::R, uint64_t>>::Cons>(
                    (*_write)->v_mut())
                    .l;
      _loop_n = m;
      continue;
    }
  }
  return std::move(*_head);
}

std::pair<ComprehensivePatterns::R, uint64_t>
ComprehensivePatterns::cond_pair(bool b, ComprehensivePatterns::R r) {
  if (b) {
    return std::make_pair(r, r.val);
  } else {
    return std::make_pair(r, r.dat);
  }
}

uint64_t ComprehensivePatterns::nested_match(
    const std::optional<ComprehensivePatterns::R> &o1,
    const std::optional<ComprehensivePatterns::R> &o2) {
  if (o1.has_value()) {
    const ComprehensivePatterns::R &r1 = *o1;
    if (o2.has_value()) {
      const ComprehensivePatterns::R &r2 = *o2;
      return (r1.val + r2.val);
    } else {
      return r1.val;
    }
  } else {
    return UINT64_C(0);
  }
}

std::pair<uint64_t, uint64_t>
ComprehensivePatterns::both_proj(const ComprehensivePatterns::R &r) {
  return std::make_pair(r.val, r.dat);
}

uint64_t
ComprehensivePatterns::compose_proj(const ComprehensivePatterns::R &r) {
  std::function<uint64_t(ComprehensivePatterns::R)> f =
      [](const ComprehensivePatterns::R &x) { return x.val; };
  std::function<uint64_t(ComprehensivePatterns::R)> g =
      [](const ComprehensivePatterns::R &x) { return x.dat; };
  return (f(r) + g(r));
}

std::optional<uint64_t>
ComprehensivePatterns::proj_through_option(const ComprehensivePatterns::R &r) {
  return std::make_optional<uint64_t>(r.val);
}

uint64_t ComprehensivePatterns::use_proj(uint64_t n) { return n; }

uint64_t
ComprehensivePatterns::proj_as_arg(const ComprehensivePatterns::NC &r) {
  return use_proj(r.nc_a);
}

uint64_t ComprehensivePatterns::use_two(uint64_t _x0, uint64_t _x1) {
  return (_x0 + _x1);
}

uint64_t
ComprehensivePatterns::multi_proj_args(const ComprehensivePatterns::NC &r) {
  return use_two(r.nc_a, r.nc_b);
}

uint64_t
ComprehensivePatterns::let_proj_then_base(const ComprehensivePatterns::NC &r) {
  uint64_t x = r.nc_a;
  uint64_t y = r.nc_b;
  return (x + y);
}

uint64_t ComprehensivePatterns::base_then_multi_proj(
    const ComprehensivePatterns::NC &r) {
  return ((r.nc_a + r.nc_b) + r.nc_c);
}

uint64_t
ComprehensivePatterns::proj_in_condition(const ComprehensivePatterns::NC &r) {
  if (r.nc_a == UINT64_C(0)) {
    return r.nc_b;
  } else {
    return r.nc_c;
  }
}

uint64_t
ComprehensivePatterns::proj_in_scrutinee(const ComprehensivePatterns::NC &r) {
  if (r.nc_a <= 0) {
    return r.nc_b;
  } else {
    uint64_t n = r.nc_a - 1;
    return (n + r.nc_c);
  }
}

uint64_t
ComprehensivePatterns::return_proj_nc(const ComprehensivePatterns::NC &r) {
  return r.nc_a;
}

uint64_t
ComprehensivePatterns::call_return_proj(const ComprehensivePatterns::NC &r) {
  return (return_proj_nc(r) + r.nc_b);
}

uint64_t ComprehensivePatterns::inc(uint64_t n) { return (n + UINT64_C(1)); }

uint64_t
ComprehensivePatterns::nested_proj_calls(const ComprehensivePatterns::NC &r) {
  return (inc(r.nc_a) + inc(r.nc_b));
}

uint64_t ComprehensivePatterns::count_down(
    uint64_t n,
    const ComprehensivePatterns::NC
        &r) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume_m: saves [_s0], resumes after recursive call with _result.
  struct _Resume_m {
    decltype(std::declval<const ComprehensivePatterns::NC &>().nc_b) _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_m>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified count_down: _Enter -> _Resume_m.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = r.nc_a;
      } else {
        uint64_t m = n - 1;
        _stack.emplace_back(_Resume_m{r.nc_b});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      auto _f = std::move(std::get<_Resume_m>(_frame));
      _result = (_result + _f._s0);
    }
  }
  return _result;
}

uint64_t ComprehensivePatterns::f1(const ComprehensivePatterns::NC &r) {
  return r.nc_a;
}

uint64_t ComprehensivePatterns::f2(const ComprehensivePatterns::NC &r) {
  return r.nc_b;
}

uint64_t ComprehensivePatterns::multi_function_calls(
    const ComprehensivePatterns::NC &r) {
  return (f1(r) + f2(r));
}

uint64_t
ComprehensivePatterns::proj_then_match(const ComprehensivePatterns::NC &r) {
  uint64_t x = r.nc_a;
  std::any _x = r.nc_a;
  uint64_t b = r.nc_b;
  std::any _x0 = r.nc_c;
  return (x + b);
}

uint64_t
ComprehensivePatterns::let_used_twice(const ComprehensivePatterns::NC &r) {
  uint64_t x = r.nc_a;
  return (x + x);
}

bool ComprehensivePatterns::base_in_call_and_proj(
    const ComprehensivePatterns::NC &r) {
  return r.nc_a == r.nc_a;
}

uint64_t ComprehensivePatterns::chained_lets_same_base(
    const ComprehensivePatterns::NC &r) {
  uint64_t x = r.nc_a;
  uint64_t y = r.nc_b;
  uint64_t z = r.nc_c;
  return ((x + y) + z);
}

uint64_t
ComprehensivePatterns::double_proj_nc(const ComprehensivePatterns::OuterNC &o) {
  return (o.outer_nc.nc_a + o.outer_nc.nc_b);
}

uint64_t
ComprehensivePatterns::multi_positions(const ComprehensivePatterns::NC &r) {
  return (r.nc_a + (r.nc_b == UINT64_C(0) ? r.nc_a : r.nc_c));
}

uint64_t ComprehensivePatterns::sum_proj(
    uint64_t n,
    const ComprehensivePatterns::NC
        &r) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume_m: saves [_s0], resumes after recursive call with _result.
  struct _Resume_m {
    decltype(std::declval<const ComprehensivePatterns::NC &>().nc_a) _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_m>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified sum_proj: _Enter -> _Resume_m.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t m = n - 1;
        _stack.emplace_back(_Resume_m{r.nc_a});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      auto _f = std::move(std::get<_Resume_m>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

uint64_t ComprehensivePatterns::hof_test(const ComprehensivePatterns::NC &r) {
  return apply(
      [](const ComprehensivePatterns::NC &x) { return (x.nc_a + x.nc_b); }, r);
}

uint64_t ComprehensivePatterns::use_two_fc(uint64_t _x0, uint64_t _x1) {
  return (_x0 + _x1);
}

uint64_t
ComprehensivePatterns::bug_two_args(const ComprehensivePatterns::State &s) {
  return use_two_fc(s.state_value, s.state_data);
}

uint64_t ComprehensivePatterns::use_three(uint64_t x, uint64_t y, uint64_t z) {
  return ((x + y) + z);
}

uint64_t
ComprehensivePatterns::bug_three_args(const ComprehensivePatterns::State &s) {
  return use_three(s.state_value, s.state_data, s.state_value);
}

uint64_t
ComprehensivePatterns::take_state_and_val(const ComprehensivePatterns::State &,
                                          uint64_t n) {
  return n;
}

uint64_t ComprehensivePatterns::bug_state_and_proj(
    const ComprehensivePatterns::State &s) {
  return take_state_and_val(s, s.state_value);
}

uint64_t ComprehensivePatterns::inner_func(uint64_t n) {
  return (n + UINT64_C(1));
}

uint64_t
ComprehensivePatterns::bug_nested_calls(const ComprehensivePatterns::State &s) {
  return use_two_fc(inner_func(s.state_value), inner_func(s.state_data));
}

uint64_t
ComprehensivePatterns::bug_in_condition(const ComprehensivePatterns::State &s) {
  if (s.state_value == UINT64_C(0)) {
    return s.state_data;
  } else {
    return s.state_value;
  }
}

uint64_t ComprehensivePatterns::f1_fc(uint64_t n) { return n; }

uint64_t ComprehensivePatterns::f2_fc(uint64_t n) { return (n + UINT64_C(1)); }

uint64_t
ComprehensivePatterns::bug_multi_calls(const ComprehensivePatterns::State &s) {
  uint64_t v = s.state_value;
  return (f1_fc(v) + f2_fc(v));
}

std::pair<ComprehensivePatterns::State, uint64_t>
ComprehensivePatterns::bug_base_and_proj(
    const ComprehensivePatterns::State &s) {
  ComprehensivePatterns::State s2 = _bug_base_and_proj_consume(s);
  return std::make_pair(s2, s2.state_value);
}

uint64_t
ComprehensivePatterns::sequential_lets(const ComprehensivePatterns::State &s) {
  return s.state_value;
}

std::pair<ComprehensivePatterns::State, uint64_t>
ComprehensivePatterns::let_then_use_base(ComprehensivePatterns::State s) {
  uint64_t v = s.state_value;
  return std::make_pair(std::move(s), v);
}

uint64_t ComprehensivePatterns::two_proj_sequence(
    const ComprehensivePatterns::State &s) {
  uint64_t v = s.state_value;
  uint64_t d = s.state_data;
  return (v + d);
}

uint64_t
ComprehensivePatterns::let_multi_proj(const ComprehensivePatterns::State &s) {
  uint64_t v = s.state_value;
  uint64_t d = s.state_data;
  return (v + d);
}

uint64_t ComprehensivePatterns::nested_lets_same_base(
    const ComprehensivePatterns::State &s) {
  uint64_t v = s.state_value;
  uint64_t d = s.state_data;
  return (v + d);
}

uint64_t
ComprehensivePatterns::if_with_proj(const ComprehensivePatterns::State &s) {
  if (s.state_value == UINT64_C(0)) {
    return s.state_data;
  } else {
    return s.state_value;
  }
}

uint64_t ComprehensivePatterns::match_scrutinee_proj(
    const ComprehensivePatterns::State &s) {
  if (s.state_value <= 0) {
    return s.state_data;
  } else {
    uint64_t n = s.state_value - 1;
    return n;
  }
}

std::pair<ComprehensivePatterns::State, uint64_t>
ComprehensivePatterns::bind_proj_use_base(ComprehensivePatterns::State s) {
  uint64_t v = s.state_value;
  return std::make_pair(std::move(s), v);
}

ComprehensivePatterns::RSeq
ComprehensivePatterns::side_effect(ComprehensivePatterns::RSeq r) {
  return r;
}

uint64_t
ComprehensivePatterns::after_side_effect(const ComprehensivePatterns::RSeq &r) {
  ComprehensivePatterns::RSeq r2 = side_effect(r);
  return std::move(r2).seq_val;
}

uint64_t
ComprehensivePatterns::two_side_effects(const ComprehensivePatterns::RSeq &r) {
  ComprehensivePatterns::RSeq r2 = side_effect(r);
  ComprehensivePatterns::RSeq r3 = side_effect(std::move(r2));
  return std::move(r3).seq_val;
}

uint64_t ComprehensivePatterns::side_effect_in_branch(
    bool b, const ComprehensivePatterns::RSeq &r) {
  ComprehensivePatterns::RSeq r2;
  if (b) {
    r2 = side_effect(r);
  } else {
    r2 = r;
  }
  return std::move(r2).seq_val;
}

uint64_t ComprehensivePatterns::return_proj_stmt(
    const ComprehensivePatterns::StateStmt &s) {
  return s.stmt_value;
}

uint64_t ComprehensivePatterns::return_complex(
    const ComprehensivePatterns::StateStmt &s) {
  return (s.stmt_value + s.stmt_data);
}

std::pair<uint64_t, uint64_t>
ComprehensivePatterns::return_pair(const ComprehensivePatterns::StateStmt &s) {
  return std::make_pair(s.stmt_value, s.stmt_data);
}

uint64_t
ComprehensivePatterns::chained_proj(const ComprehensivePatterns::OuterStmt &o) {
  return o.outer_stmt_inner.inner_stmt_val;
}

uint64_t ComprehensivePatterns::triple_chain(
    const ComprehensivePatterns::Level3Stmt &l3) {
  return l3.l3_outer_stmt.outer_stmt_inner.inner_stmt_val;
}

uint64_t ComprehensivePatterns::proj_in_arith(
    const ComprehensivePatterns::StateStmt &s) {
  return (s.stmt_value + UINT64_C(10));
}

uint64_t ComprehensivePatterns::multi_proj_expr(
    const ComprehensivePatterns::StateStmt &s) {
  return (s.stmt_value + (s.stmt_data * UINT64_C(2)));
}

List<uint64_t>
ComprehensivePatterns::proj_in_list(const ComprehensivePatterns::StateStmt &s) {
  return List<uint64_t>::cons(
      s.stmt_value, List<uint64_t>::cons(s.stmt_data, List<uint64_t>::nil()));
}

bool ComprehensivePatterns::compare_projs(
    const ComprehensivePatterns::StateStmt &s) {
  return s.stmt_value == s.stmt_data;
}

bool ComprehensivePatterns::bool_with_proj(
    const ComprehensivePatterns::StateStmt &s) {
  return !(s.stmt_value == UINT64_C(0));
}

uint64_t ComprehensivePatterns::sum_values(
    uint64_t n,
    const ComprehensivePatterns::StateStmt
        &s) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume_m: saves [_s0], resumes after recursive call with _result.
  struct _Resume_m {
    decltype(std::declval<const ComprehensivePatterns::StateStmt &>()
                 .stmt_value) _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_m>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified sum_values: _Enter -> _Resume_m.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t m = n - 1;
        _stack.emplace_back(_Resume_m{s.stmt_value});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      auto _f = std::move(std::get<_Resume_m>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

uint64_t
ComprehensivePatterns::branch_use(bool b, const ComprehensivePatterns::RCF &r) {
  if (b) {
    return r.cf_val;
  } else {
    return r.cf_val;
  }
}

std::pair<ComprehensivePatterns::RCF, uint64_t>
ComprehensivePatterns::branch_different(bool b, ComprehensivePatterns::RCF r) {
  if (b) {
    return std::make_pair(r, r.cf_val);
  } else {
    return std::make_pair(std::move(r), UINT64_C(0));
  }
}

uint64_t ComprehensivePatterns::match_with_wild(
    const std::optional<ComprehensivePatterns::RCF> &o) {
  if (o.has_value()) {
    const ComprehensivePatterns::RCF &r = *o;
    return r.cf_val;
  } else {
    return UINT64_C(0);
  }
}

uint64_t ComprehensivePatterns::sum_with_state(
    uint64_t n,
    const ComprehensivePatterns::RCF
        &r) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume_m: saves [_s0], resumes after recursive call with _result.
  struct _Resume_m {
    decltype(std::declval<const ComprehensivePatterns::RCF &>().cf_val) _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_m>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified sum_with_state: _Enter -> _Resume_m.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = r.cf_val;
      } else {
        uint64_t m = n - 1;
        _stack.emplace_back(_Resume_m{r.cf_val});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      auto _f = std::move(std::get<_Resume_m>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

uint64_t
ComprehensivePatterns::even_count(uint64_t n,
                                  const ComprehensivePatterns::RCF &r) {
  if (n <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t m = n - 1;
    return (UINT64_C(1) + odd_count(m, r));
  }
}

uint64_t ComprehensivePatterns::odd_count(uint64_t n,
                                          const ComprehensivePatterns::RCF &r) {
  if (n <= 0) {
    return r.cf_val;
  } else {
    uint64_t m = n - 1;
    return (UINT64_C(1) + even_count(m, r));
  }
}

uint64_t ComprehensivePatterns::accum_with_state(
    uint64_t n,
    const ComprehensivePatterns::StateLB
        &s) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume_m: saves [_s0], resumes after recursive call with _result.
  struct _Resume_m {
    decltype(std::declval<const ComprehensivePatterns::StateLB &>()
                 .lb_value) _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_m>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified accum_with_state: _Enter -> _Resume_m.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = s.lb_value;
      } else {
        uint64_t m = n - 1;
        _stack.emplace_back(_Resume_m{s.lb_value});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      auto _f = std::move(std::get<_Resume_m>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

ComprehensivePatterns::StateOP
ComprehensivePatterns::identity(ComprehensivePatterns::StateOP s) {
  return s;
}

uint64_t ComprehensivePatterns::extract_via_match(
    const ComprehensivePatterns::StateOP &s) {
  return identity(s).op_value;
}

ComprehensivePatterns::StateOP
ComprehensivePatterns::consume_state(ComprehensivePatterns::StateOP s) {
  return s;
}

uint64_t
ComprehensivePatterns::match_consumed(const ComprehensivePatterns::StateOP &s) {
  return consume_state(s).op_value;
}

std::pair<ComprehensivePatterns::StateOP, uint64_t>
ComprehensivePatterns::force_owned(ComprehensivePatterns::StateOP s) {
  uint64_t result = s.op_value;
  return std::make_pair(std::move(s), result);
}

std::pair<
    std::pair<ComprehensivePatterns::StateOP, ComprehensivePatterns::StateOP>,
    uint64_t>
ComprehensivePatterns::pair_then_match(ComprehensivePatterns::StateOP s) {
  std::pair<ComprehensivePatterns::StateOP, ComprehensivePatterns::StateOP> p =
      std::make_pair(s, s);
  uint64_t x = std::move(s).op_value;
  return std::make_pair(p, x);
}
