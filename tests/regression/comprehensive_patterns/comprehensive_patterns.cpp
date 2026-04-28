#include <comprehensive_patterns.h>

__attribute__((pure))
std::pair<std::pair<ComprehensivePatterns::S, unsigned int>, unsigned int>
ComprehensivePatterns::syntactic_variation(ComprehensivePatterns::S s) {
  unsigned int a = s.s_a;
  std::function<unsigned int(ComprehensivePatterns::S)> b =
      [](const ComprehensivePatterns::S &s0) { return s0.s_b; };
  return std::make_pair(std::make_pair(s, a), b(s));
}

__attribute__((pure)) std::pair<ComprehensivePatterns::S, unsigned int>
ComprehensivePatterns::with_magic(ComprehensivePatterns::S s) {
  return std::make_pair(s, s.s_a);
}

__attribute__((pure)) std::pair<
    std::pair<
        std::pair<std::pair<std::pair<std::pair<ComprehensivePatterns::L5,
                                                ComprehensivePatterns::L4>,
                                      ComprehensivePatterns::L3>,
                            ComprehensivePatterns::L2>,
                  ComprehensivePatterns::L1>,
        ComprehensivePatterns::S>,
    unsigned int>
ComprehensivePatterns::deep_nest(ComprehensivePatterns::L5 l5) {
  ComprehensivePatterns::L4 l4 = l5.l5_l4;
  ComprehensivePatterns::L3 l3 = l4.l4_l3;
  ComprehensivePatterns::L2 l2 = l3.l3_l2;
  ComprehensivePatterns::L1 l1 = l2.l2_l1;
  ComprehensivePatterns::S s = l1.l1_s;
  return std::make_pair(
      std::make_pair(
          std::make_pair(
              std::make_pair(
                  std::make_pair(std::make_pair(std::move(l5), std::move(l4)),
                                 std::move(l3)),
                  std::move(l2)),
              std::move(l1)),
          s),
      s.s_a);
}

__attribute__((pure)) std::pair<
    std::pair<std::pair<ComprehensivePatterns::S, unsigned int>, unsigned int>,
    unsigned int>
ComprehensivePatterns::nested_pair_reuse(ComprehensivePatterns::S s) {
  return std::make_pair(std::make_pair(std::make_pair(s, s.s_a), s.s_b), s.s_c);
}

__attribute__((pure)) std::pair<ComprehensivePatterns::S, unsigned int>
ComprehensivePatterns::compose(ComprehensivePatterns::S s) {
  std::function<unsigned int(ComprehensivePatterns::S)> f =
      [](const ComprehensivePatterns::S &x) { return x.s_a; };
  return std::make_pair(s, f(s));
}

__attribute__((pure))
std::pair<std::function<unsigned int(unsigned int)>, ComprehensivePatterns::S>
ComprehensivePatterns::lambda_proj(ComprehensivePatterns::S s) {
  return std::make_pair([=](const unsigned int &) mutable { return s.s_a; }, s);
}

__attribute__((pure)) std::pair<
    std::pair<std::pair<ComprehensivePatterns::S, unsigned int>, unsigned int>,
    unsigned int>
ComprehensivePatterns::proj_chain(ComprehensivePatterns::S s) {
  unsigned int a = s.s_a;
  unsigned int b = s.s_b;
  unsigned int c = s.s_c;
  return std::make_pair(std::make_pair(std::make_pair(std::move(s), a), b), c);
}

__attribute__((pure)) std::pair<
    std::pair<std::pair<ComprehensivePatterns::S, ComprehensivePatterns::S>,
              std::pair<unsigned int, unsigned int>>,
    std::pair<std::pair<unsigned int, unsigned int>,
              std::pair<unsigned int, unsigned int>>>
ComprehensivePatterns::octuple(ComprehensivePatterns::S s) {
  return std::make_pair(
      std::make_pair(std::make_pair(s, s), std::make_pair(s.s_a, s.s_b)),
      std::make_pair(std::make_pair(s.s_c, s.s_a),
                     std::make_pair(s.s_b, s.s_c)));
}

__attribute__((pure))
std::pair<std::optional<std::pair<ComprehensivePatterns::S, unsigned int>>,
          ComprehensivePatterns::S>
ComprehensivePatterns::nested_containers(ComprehensivePatterns::S s) {
  return std::make_pair(
      std::make_optional<std::pair<ComprehensivePatterns::S, unsigned int>>(
          std::make_pair(s, s.s_a)),
      s);
}

__attribute__((pure))
std::pair<std::pair<ComprehensivePatterns::S, unsigned int>, unsigned int>
ComprehensivePatterns::match_pair(
    const std::pair<ComprehensivePatterns::S, unsigned int> &p) {
  const ComprehensivePatterns::S &s = p.first;
  const unsigned int &n = p.second;
  return std::make_pair(std::make_pair(s, n), s.s_a);
}

__attribute__((pure)) List<std::pair<ComprehensivePatterns::S, unsigned int>>
ComprehensivePatterns::make_list(const unsigned int &n,
                                 ComprehensivePatterns::S s) {
  std::unique_ptr<List<std::pair<ComprehensivePatterns::S, unsigned int>>>
      _head{};
  std::unique_ptr<List<std::pair<ComprehensivePatterns::S, unsigned int>>>
      *_write = &_head;
  unsigned int _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      *(_write) = std::make_unique<
          List<std::pair<ComprehensivePatterns::S, unsigned int>>>(
          List<std::pair<ComprehensivePatterns::S, unsigned int>>::nil());
      break;
    } else {
      unsigned int m = _loop_n - 1;
      auto _cell = std::make_unique<
          List<std::pair<ComprehensivePatterns::S, unsigned int>>>(
          typename List<std::pair<ComprehensivePatterns::S, unsigned int>>::
              Cons(std::make_pair(s, s.s_a), nullptr));
      *(_write) = std::move(_cell);
      _write = &std::get<typename List<
          std::pair<ComprehensivePatterns::S, unsigned int>>::Cons>(
                    (*_write)->v_mut())
                    .d_a1;
      _loop_n = m;
      continue;
    }
  }
  return std::move(*(_head));
}

__attribute__((pure))
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

__attribute__((pure)) std::pair<ComprehensivePatterns::S, unsigned int>
ComprehensivePatterns::match_three(const ComprehensivePatterns::Three t,
                                   ComprehensivePatterns::S s) {
  switch (t) {
  case Three::e_A: {
    return std::make_pair(s, s.s_a);
  }
  case Three::e_B: {
    return std::make_pair(s, s.s_b);
  }
  case Three::e_C: {
    return std::make_pair(s, s.s_c);
  }
  default:
    std::unreachable();
  }
}

__attribute__((pure)) std::pair<ComprehensivePatterns::S, unsigned int>
ComprehensivePatterns::let_in_arg(ComprehensivePatterns::S s) {
  return std::make_pair(s, s.s_a);
}

__attribute__((pure)) std::pair<ComprehensivePatterns::S, unsigned int>
ComprehensivePatterns::match_record(ComprehensivePatterns::S s) {
  unsigned int a = s.s_a;
  std::any _x = s.s_b;
  std::any _x0 = s.s_c;
  return std::make_pair(s, a);
}

__attribute__((pure)) std::pair<ComprehensivePatterns::S, unsigned int>
ComprehensivePatterns::rebind(ComprehensivePatterns::S s1) {
  return std::make_pair(s1, s1.s_a);
}

__attribute__((pure)) std::pair<std::function<unsigned int(std::monostate)>,
                                std::function<unsigned int(std::monostate)>>
ComprehensivePatterns::closure_pair(ComprehensivePatterns::S s) {
  return std::make_pair([=](const std::monostate &) mutable { return s.s_a; },
                        [=](const std::monostate &) mutable { return s.s_b; });
}

__attribute__((pure)) Sig<ComprehensivePatterns::S>
ComprehensivePatterns::sigma_reuse(ComprehensivePatterns::S s) {
  return Sig<ComprehensivePatterns::S>::exist(std::move(s));
}

__attribute__((pure))
std::pair<unsigned int, std::pair<unsigned int, unsigned int>>
ComprehensivePatterns::multi_proj_arg(const ComprehensivePatterns::S &s) {
  return std::make_pair(s.s_a, std::make_pair(s.s_a, s.s_b));
}

__attribute__((pure))
std::pair<ComprehensivePatterns::Either, ComprehensivePatterns::Either>
ComprehensivePatterns::both_in_sum(ComprehensivePatterns::S s) {
  return std::make_pair(Either::left_s(s), Either::right_n(s.s_a));
}

__attribute__((pure)) std::pair<
    std::pair<std::pair<ComprehensivePatterns::R3, ComprehensivePatterns::R2>,
              ComprehensivePatterns::R1>,
    unsigned int>
ComprehensivePatterns::hard_proj_chain(ComprehensivePatterns::R3 r3) {
  ComprehensivePatterns::R2 r2 = r3.r3_r2;
  ComprehensivePatterns::R1 r1 = r2.r2_inner;
  return std::make_pair(
      std::make_pair(std::make_pair(std::move(r3), std::move(r2)), r1),
      r1.r1_val);
}

__attribute__((pure))
std::pair<std::pair<ComprehensivePatterns::R2, ComprehensivePatterns::R1>,
          unsigned int>
ComprehensivePatterns::multi_path(const ComprehensivePatterns::R3 &r3) {
  return std::make_pair(std::make_pair(r3.r3_r2, r3.r3_r2.r2_inner),
                        r3.r3_r2.r2_inner.r1_val);
}

__attribute__((pure))
std::pair<std::pair<ComprehensivePatterns::R2, ComprehensivePatterns::R1>,
          unsigned int>
ComprehensivePatterns::let_proj(ComprehensivePatterns::R2 r2) {
  ComprehensivePatterns::R1 r1 = r2.r2_inner;
  unsigned int n = r1.r1_val;
  return std::make_pair(std::make_pair(std::move(r2), std::move(r1)), n);
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::extract_val(const ComprehensivePatterns::R1 &r1) {
  return r1.r1_val;
}

__attribute__((pure)) std::pair<ComprehensivePatterns::R2, unsigned int>
ComprehensivePatterns::nested_call(ComprehensivePatterns::R2 r2) {
  return std::make_pair(r2, extract_val(r2.r2_inner));
}

__attribute__((pure))
std::pair<std::pair<ComprehensivePatterns::R2, ComprehensivePatterns::R1>,
          unsigned int>
ComprehensivePatterns::multi_proj_let(unsigned int n) {
  ComprehensivePatterns::R2 r2 = R2{R1{n}, n};
  return std::make_pair(std::make_pair(r2, r2.r2_inner), r2.r2_data);
}

__attribute__((pure))
std::optional<std::pair<ComprehensivePatterns::R2, ComprehensivePatterns::R1>>
ComprehensivePatterns::match_proj(ComprehensivePatterns::R2 r2) {
  ComprehensivePatterns::R1 r1 = r2.r2_inner;
  return std::make_optional<
      std::pair<ComprehensivePatterns::R2, ComprehensivePatterns::R1>>(
      std::make_pair(std::move(r2), std::move(r1)));
}

__attribute__((pure))
std::pair<std::pair<ComprehensivePatterns::R1, unsigned int>, unsigned int>
ComprehensivePatterns::proj_multi_use(const ComprehensivePatterns::R2 &r2) {
  const ComprehensivePatterns::R1 &r1 = r2.r2_inner;
  return std::make_pair(std::make_pair(r1, r1.r1_val), r1.r1_val);
}

__attribute__((pure))
std::pair<std::pair<ComprehensivePatterns::R3, ComprehensivePatterns::R2>,
          std::pair<ComprehensivePatterns::R1, unsigned int>>
ComprehensivePatterns::complex_nest(ComprehensivePatterns::R3 r3) {
  return std::make_pair(
      std::make_pair(r3, r3.r3_r2),
      std::make_pair(r3.r3_r2.r2_inner, r3.r3_r2.r2_inner.r1_val));
}

__attribute__((pure)) ComprehensivePatterns::R2
ComprehensivePatterns::make_r2(unsigned int n) {
  return R2{R1{n}, n};
}

__attribute__((pure))
std::pair<std::pair<ComprehensivePatterns::R2, ComprehensivePatterns::R1>,
          unsigned int>
ComprehensivePatterns::from_func(const unsigned int &n) {
  ComprehensivePatterns::R2 r2 = make_r2(n);
  return std::make_pair(std::make_pair(r2, r2.r2_inner), r2.r2_data);
}

__attribute__((pure))
std::pair<std::pair<ComprehensivePatterns::R2, ComprehensivePatterns::R1>,
          std::pair<ComprehensivePatterns::R1, unsigned int>>
ComprehensivePatterns::pair_of_pairs(ComprehensivePatterns::R2 r2) {
  ComprehensivePatterns::R1 r1 = r2.r2_inner;
  return std::make_pair(std::make_pair(std::move(r2), r1),
                        std::make_pair(r1, r1.r1_val));
}

__attribute__((pure))
std::pair<ComprehensivePatterns::R2, ComprehensivePatterns::R1>
ComprehensivePatterns::cond_proj(const bool &b, ComprehensivePatterns::R2 r2) {
  if (b) {
    return std::make_pair(r2, r2.r2_inner);
  } else {
    return std::make_pair(r2, r2.r2_inner);
  }
}

__attribute__((pure))
List<std::pair<ComprehensivePatterns::R2, ComprehensivePatterns::R1>>
ComprehensivePatterns::repeat_r2(const unsigned int &n,
                                 ComprehensivePatterns::R2 r2) {
  std::unique_ptr<
      List<std::pair<ComprehensivePatterns::R2, ComprehensivePatterns::R1>>>
      _head{};
  std::unique_ptr<
      List<std::pair<ComprehensivePatterns::R2, ComprehensivePatterns::R1>>>
      *_write = &_head;
  unsigned int _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      *(_write) = std::make_unique<List<
          std::pair<ComprehensivePatterns::R2, ComprehensivePatterns::R1>>>(
          List<std::pair<ComprehensivePatterns::R2,
                         ComprehensivePatterns::R1>>::nil());
      break;
    } else {
      unsigned int m = _loop_n - 1;
      auto _cell = std::make_unique<List<
          std::pair<ComprehensivePatterns::R2, ComprehensivePatterns::R1>>>(
          typename List<
              std::pair<ComprehensivePatterns::R2, ComprehensivePatterns::R1>>::
              Cons(std::make_pair(r2, r2.r2_inner), nullptr));
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename List<std::pair<ComprehensivePatterns::R2,
                                            ComprehensivePatterns::R1>>::Cons>(
               (*_write)->v_mut())
               .d_a1;
      _loop_n = m;
      continue;
    }
  }
  return std::move(*(_head));
}

__attribute__((pure))
std::pair<std::pair<ComprehensivePatterns::R3, ComprehensivePatterns::R2>,
          ComprehensivePatterns::R1>
ComprehensivePatterns::nested_lets(ComprehensivePatterns::R3 r3) {
  ComprehensivePatterns::R2 r2 = r3.r3_r2;
  ComprehensivePatterns::R1 r1 = r2.r2_inner;
  return std::make_pair(std::make_pair(std::move(r3), std::move(r2)),
                        std::move(r1));
}

__attribute__((pure)) std::pair<ComprehensivePatterns::R1, unsigned int>
ComprehensivePatterns::double_proj(const ComprehensivePatterns::R3 &r3) {
  return std::make_pair(r3.r3_r2.r2_inner, r3.r3_r2.r2_inner.r1_val);
}

__attribute__((pure))
std::pair<std::pair<ComprehensivePatterns::R3, ComprehensivePatterns::R2>,
          ComprehensivePatterns::R2>
ComprehensivePatterns::mixed_access(ComprehensivePatterns::R3 r3) {
  ComprehensivePatterns::R2 r2 = r3.r3_r2;
  return std::make_pair(std::make_pair(r3, std::move(r2)), r3.r3_r2);
}

__attribute__((pure))
std::pair<ComprehensivePatterns::R2, ComprehensivePatterns::R1>
ComprehensivePatterns::return_proj_h(ComprehensivePatterns::R2 r2) {
  return std::make_pair(r2, r2.r2_inner);
}

__attribute__((pure)) std::pair<
    std::pair<std::pair<ComprehensivePatterns::R3, ComprehensivePatterns::R2>,
              ComprehensivePatterns::R1>,
    unsigned int>
ComprehensivePatterns::all_levels(ComprehensivePatterns::R3 r3) {
  return std::make_pair(
      std::make_pair(std::make_pair(r3, r3.r3_r2), r3.r3_r2.r2_inner),
      r3.r3_r2.r2_inner.r1_val);
}

__attribute__((pure))
std::pair<ComprehensivePatterns::R1, ComprehensivePatterns::R1>
ComprehensivePatterns::let_and_proj(const ComprehensivePatterns::R2 &r2) {
  const ComprehensivePatterns::R1 &r1 = r2.r2_inner;
  return std::make_pair(r1, r2.r2_inner);
}

__attribute__((pure))
std::pair<ComprehensivePatterns::R2, ComprehensivePatterns::R2>
ComprehensivePatterns::multi_construct(ComprehensivePatterns::R1 r1) {
  ComprehensivePatterns::R2 r2a = R2{r1, 0u};
  ComprehensivePatterns::R2 r2b = R2{r1, 1u};
  return std::make_pair(std::move(r2a), std::move(r2b));
}

__attribute__((pure))
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

__attribute__((pure)) std::pair<ComprehensivePatterns::R, unsigned int>
ComprehensivePatterns::pair_inline_proj(ComprehensivePatterns::R r) {
  return std::make_pair(r, r.val);
}

__attribute__((pure))
std::pair<std::pair<ComprehensivePatterns::R, unsigned int>, unsigned int>
ComprehensivePatterns::nested_pair_inline(ComprehensivePatterns::R r) {
  return std::make_pair(std::make_pair(r, r.val), r.dat);
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::match_bind_and_use(const ComprehensivePatterns::R &r) {
  unsigned int v = r.val;
  unsigned int d = r.dat;
  return ((v + d) + r.val);
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::let_with_type(const ComprehensivePatterns::R &r) {
  return (r.val + r.val);
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::proj_of_last_use(const ComprehensivePatterns::R &r1) {
  return r1.val;
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::multi_let_same(const ComprehensivePatterns::R &r) {
  return ((r.val + r.val) + r.val);
}

__attribute__((pure)) unsigned int ComprehensivePatterns::option_unwrap_proj(
    const std::optional<ComprehensivePatterns::R> &o) {
  if (o.has_value()) {
    const ComprehensivePatterns::R &r = *o;
    return (r.val + r.dat);
  } else {
    return 0u;
  }
}

__attribute__((pure)) std::pair<ComprehensivePatterns::R, unsigned int>
ComprehensivePatterns::fun_result_and_proj(unsigned int n) {
  ComprehensivePatterns::R r = R{n, n};
  return std::make_pair(r, r.val);
}

__attribute__((pure)) std::optional<unsigned int>
ComprehensivePatterns::match_multi_use(
    const std::optional<ComprehensivePatterns::R> &o) {
  if (o.has_value()) {
    const ComprehensivePatterns::R &r = *o;
    return std::make_optional<unsigned int>((r.val + r.dat));
  } else {
    return std::optional<unsigned int>();
  }
}

__attribute__((pure))
std::pair<std::pair<ComprehensivePatterns::R, unsigned int>, unsigned int>
ComprehensivePatterns::tuple_proj(ComprehensivePatterns::R r) {
  return std::make_pair(std::make_pair(r, r.val), r.dat);
}

__attribute__((pure)) std::pair<ComprehensivePatterns::R, unsigned int>
ComprehensivePatterns::chain_to_pair(ComprehensivePatterns::R r1) {
  return std::make_pair(r1, r1.val);
}

__attribute__((pure)) List<std::pair<ComprehensivePatterns::R, unsigned int>>
ComprehensivePatterns::repeat_pair(const unsigned int &n,
                                   ComprehensivePatterns::R r) {
  std::unique_ptr<List<std::pair<ComprehensivePatterns::R, unsigned int>>>
      _head{};
  std::unique_ptr<List<std::pair<ComprehensivePatterns::R, unsigned int>>>
      *_write = &_head;
  unsigned int _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      *(_write) = std::make_unique<
          List<std::pair<ComprehensivePatterns::R, unsigned int>>>(
          List<std::pair<ComprehensivePatterns::R, unsigned int>>::nil());
      break;
    } else {
      unsigned int m = _loop_n - 1;
      auto _cell = std::make_unique<
          List<std::pair<ComprehensivePatterns::R, unsigned int>>>(
          typename List<std::pair<ComprehensivePatterns::R, unsigned int>>::
              Cons(std::make_pair(r, r.val), nullptr));
      *(_write) = std::move(_cell);
      _write = &std::get<typename List<
          std::pair<ComprehensivePatterns::R, unsigned int>>::Cons>(
                    (*_write)->v_mut())
                    .d_a1;
      _loop_n = m;
      continue;
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) std::pair<ComprehensivePatterns::R, unsigned int>
ComprehensivePatterns::cond_pair(const bool &b, ComprehensivePatterns::R r) {
  if (b) {
    return std::make_pair(r, r.val);
  } else {
    return std::make_pair(r, r.dat);
  }
}

__attribute__((pure)) unsigned int ComprehensivePatterns::nested_match(
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
    return 0u;
  }
}

__attribute__((pure)) std::pair<unsigned int, unsigned int>
ComprehensivePatterns::both_proj(const ComprehensivePatterns::R &r) {
  return std::make_pair(r.val, r.dat);
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::compose_proj(const ComprehensivePatterns::R &r) {
  std::function<unsigned int(ComprehensivePatterns::R)> f =
      [](const ComprehensivePatterns::R &x) { return x.val; };
  std::function<unsigned int(ComprehensivePatterns::R)> g =
      [](const ComprehensivePatterns::R &x) { return x.dat; };
  return (f(r) + g(r));
}

__attribute__((pure)) std::optional<unsigned int>
ComprehensivePatterns::proj_through_option(const ComprehensivePatterns::R &r) {
  return std::make_optional<unsigned int>(r.val);
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::use_proj(unsigned int n) {
  return n;
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::proj_as_arg(const ComprehensivePatterns::NC &r) {
  return use_proj(r.nc_a);
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::use_two(const unsigned int &_x0,
                               const unsigned int &_x1) {
  return (_x0 + _x1);
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::multi_proj_args(const ComprehensivePatterns::NC &r) {
  return use_two(r.nc_a, r.nc_b);
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::let_proj_then_base(const ComprehensivePatterns::NC &r) {
  unsigned int x = r.nc_a;
  unsigned int y = r.nc_b;
  return (x + y);
}

__attribute__((pure)) unsigned int ComprehensivePatterns::base_then_multi_proj(
    const ComprehensivePatterns::NC &r) {
  return ((r.nc_a + r.nc_b) + r.nc_c);
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::proj_in_condition(const ComprehensivePatterns::NC &r) {
  if (r.nc_a == 0u) {
    return r.nc_b;
  } else {
    return r.nc_c;
  }
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::proj_in_scrutinee(const ComprehensivePatterns::NC &r) {
  if (r.nc_a <= 0) {
    return r.nc_b;
  } else {
    unsigned int n = r.nc_a - 1;
    return (n + r.nc_c);
  }
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::return_proj_nc(const ComprehensivePatterns::NC &r) {
  return r.nc_a;
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::call_return_proj(const ComprehensivePatterns::NC &r) {
  return (return_proj_nc(r) + r.nc_b);
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::inc(const unsigned int &n) {
  return (n + 1u);
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::nested_proj_calls(const ComprehensivePatterns::NC &r) {
  return (inc(r.nc_a) + inc(r.nc_b));
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::count_down(const unsigned int &n,
                                  const ComprehensivePatterns::NC &r) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    decltype((std::declval<const ComprehensivePatterns::NC &>()).nc_b) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = r.nc_a;
      } else {
        unsigned int m = n - 1;
        _stack.emplace_back(_Call1{r.nc_b});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_result + _f._s0);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::f1(const ComprehensivePatterns::NC &r) {
  return r.nc_a;
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::f2(const ComprehensivePatterns::NC &r) {
  return r.nc_b;
}

__attribute__((pure)) unsigned int ComprehensivePatterns::multi_function_calls(
    const ComprehensivePatterns::NC &r) {
  return (f1(r) + f2(r));
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::proj_then_match(const ComprehensivePatterns::NC &r) {
  unsigned int x = r.nc_a;
  std::any _x = r.nc_a;
  unsigned int b = r.nc_b;
  std::any _x0 = r.nc_c;
  return (x + b);
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::let_used_twice(const ComprehensivePatterns::NC &r) {
  unsigned int x = r.nc_a;
  return (x + x);
}

__attribute__((pure)) bool ComprehensivePatterns::base_in_call_and_proj(
    const ComprehensivePatterns::NC &r) {
  return r.nc_a == r.nc_a;
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::chained_lets_same_base(
    const ComprehensivePatterns::NC &r) {
  unsigned int x = r.nc_a;
  unsigned int y = r.nc_b;
  unsigned int z = r.nc_c;
  return ((x + y) + z);
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::double_proj_nc(const ComprehensivePatterns::OuterNC &o) {
  return (o.outer_nc.nc_a + o.outer_nc.nc_b);
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::multi_positions(const ComprehensivePatterns::NC &r) {
  return (r.nc_a + (r.nc_b == 0u ? r.nc_a : r.nc_c));
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::sum_proj(const unsigned int &n,
                                const ComprehensivePatterns::NC &r) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    decltype((std::declval<const ComprehensivePatterns::NC &>()).nc_a) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = 0u;
      } else {
        unsigned int m = n - 1;
        _stack.emplace_back(_Call1{r.nc_a});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::hof_test(const ComprehensivePatterns::NC &r) {
  return apply(
      [](const ComprehensivePatterns::NC &x) { return (x.nc_a + x.nc_b); }, r);
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::use_two_fc(const unsigned int &_x0,
                                  const unsigned int &_x1) {
  return (_x0 + _x1);
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::bug_two_args(const ComprehensivePatterns::State &s) {
  return use_two_fc(s.state_value, s.state_data);
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::use_three(const unsigned int &x, const unsigned int &y,
                                 const unsigned int &z) {
  return ((x + y) + z);
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::bug_three_args(const ComprehensivePatterns::State &s) {
  return use_three(s.state_value, s.state_data, s.state_value);
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::take_state_and_val(const ComprehensivePatterns::State &,
                                          unsigned int n) {
  return n;
}

__attribute__((pure)) unsigned int ComprehensivePatterns::bug_state_and_proj(
    const ComprehensivePatterns::State &s) {
  return take_state_and_val(s, s.state_value);
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::inner_func(const unsigned int &n) {
  return (n + 1u);
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::bug_nested_calls(const ComprehensivePatterns::State &s) {
  return use_two_fc(inner_func(s.state_value), inner_func(s.state_data));
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::bug_in_condition(const ComprehensivePatterns::State &s) {
  if (s.state_value == 0u) {
    return s.state_data;
  } else {
    return s.state_value;
  }
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::f1_fc(unsigned int n) {
  return n;
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::f2_fc(const unsigned int &n) {
  return (n + 1u);
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::bug_multi_calls(const ComprehensivePatterns::State &s) {
  unsigned int v = s.state_value;
  return (f1_fc(v) + f2_fc(v));
}

__attribute__((pure)) std::pair<ComprehensivePatterns::State, unsigned int>
ComprehensivePatterns::bug_base_and_proj(
    const ComprehensivePatterns::State &s) {
  ComprehensivePatterns::State s2 = _bug_base_and_proj_consume(s);
  return std::make_pair(s2, s2.state_value);
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::sequential_lets(const ComprehensivePatterns::State &s) {
  return s.state_value;
}

__attribute__((pure)) std::pair<ComprehensivePatterns::State, unsigned int>
ComprehensivePatterns::let_then_use_base(ComprehensivePatterns::State s) {
  unsigned int v = s.state_value;
  return std::make_pair(std::move(s), v);
}

__attribute__((pure)) unsigned int ComprehensivePatterns::two_proj_sequence(
    const ComprehensivePatterns::State &s) {
  unsigned int v = s.state_value;
  unsigned int d = s.state_data;
  return (v + d);
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::let_multi_proj(const ComprehensivePatterns::State &s) {
  unsigned int v = s.state_value;
  unsigned int d = s.state_data;
  return (v + d);
}

__attribute__((pure)) unsigned int ComprehensivePatterns::nested_lets_same_base(
    const ComprehensivePatterns::State &s) {
  unsigned int v = s.state_value;
  unsigned int d = s.state_data;
  return (v + d);
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::if_with_proj(const ComprehensivePatterns::State &s) {
  if (s.state_value == 0u) {
    return s.state_data;
  } else {
    return s.state_value;
  }
}

__attribute__((pure)) unsigned int ComprehensivePatterns::match_scrutinee_proj(
    const ComprehensivePatterns::State &s) {
  if (s.state_value <= 0) {
    return s.state_data;
  } else {
    unsigned int n = s.state_value - 1;
    return n;
  }
}

__attribute__((pure)) std::pair<ComprehensivePatterns::State, unsigned int>
ComprehensivePatterns::bind_proj_use_base(ComprehensivePatterns::State s) {
  unsigned int v = s.state_value;
  return std::make_pair(std::move(s), v);
}

__attribute__((pure)) ComprehensivePatterns::RSeq
ComprehensivePatterns::side_effect(ComprehensivePatterns::RSeq r) {
  return r;
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::after_side_effect(const ComprehensivePatterns::RSeq &r) {
  ComprehensivePatterns::RSeq r2 = side_effect(r);
  return std::move(r2).seq_val;
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::two_side_effects(const ComprehensivePatterns::RSeq &r) {
  ComprehensivePatterns::RSeq r2 = side_effect(r);
  ComprehensivePatterns::RSeq r3 = side_effect(std::move(r2));
  return std::move(r3).seq_val;
}

__attribute__((pure)) unsigned int ComprehensivePatterns::side_effect_in_branch(
    const bool &b, const ComprehensivePatterns::RSeq &r) {
  ComprehensivePatterns::RSeq r2;
  if (b) {
    r2 = side_effect(r);
  } else {
    r2 = r;
  }
  return std::move(r2).seq_val;
}

__attribute__((pure)) unsigned int ComprehensivePatterns::return_proj_stmt(
    const ComprehensivePatterns::StateStmt &s) {
  return s.stmt_value;
}

__attribute__((pure)) unsigned int ComprehensivePatterns::return_complex(
    const ComprehensivePatterns::StateStmt &s) {
  return (s.stmt_value + s.stmt_data);
}

__attribute__((pure)) std::pair<unsigned int, unsigned int>
ComprehensivePatterns::return_pair(const ComprehensivePatterns::StateStmt &s) {
  return std::make_pair(s.stmt_value, s.stmt_data);
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::chained_proj(const ComprehensivePatterns::OuterStmt &o) {
  return o.outer_stmt_inner.inner_stmt_val;
}

__attribute__((pure)) unsigned int ComprehensivePatterns::triple_chain(
    const ComprehensivePatterns::Level3Stmt &l3) {
  return l3.l3_outer_stmt.outer_stmt_inner.inner_stmt_val;
}

__attribute__((pure)) unsigned int ComprehensivePatterns::proj_in_arith(
    const ComprehensivePatterns::StateStmt &s) {
  return (s.stmt_value + 10u);
}

__attribute__((pure)) unsigned int ComprehensivePatterns::multi_proj_expr(
    const ComprehensivePatterns::StateStmt &s) {
  return (s.stmt_value + (s.stmt_data * 2u));
}

__attribute__((pure)) List<unsigned int>
ComprehensivePatterns::proj_in_list(const ComprehensivePatterns::StateStmt &s) {
  return List<unsigned int>::cons(
      s.stmt_value,
      List<unsigned int>::cons(s.stmt_data, List<unsigned int>::nil()));
}

__attribute__((pure)) bool ComprehensivePatterns::compare_projs(
    const ComprehensivePatterns::StateStmt &s) {
  return s.stmt_value == s.stmt_data;
}

__attribute__((pure)) bool ComprehensivePatterns::bool_with_proj(
    const ComprehensivePatterns::StateStmt &s) {
  return !(s.stmt_value == 0u);
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::sum_values(const unsigned int &n,
                                  const ComprehensivePatterns::StateStmt &s) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    decltype((std::declval<const ComprehensivePatterns::StateStmt &>())
                 .stmt_value) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = 0u;
      } else {
        unsigned int m = n - 1;
        _stack.emplace_back(_Call1{s.stmt_value});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::branch_use(const bool &b,
                                  const ComprehensivePatterns::RCF &r) {
  if (b) {
    return r.cf_val;
  } else {
    return r.cf_val;
  }
}

__attribute__((pure)) std::pair<ComprehensivePatterns::RCF, unsigned int>
ComprehensivePatterns::branch_different(const bool &b,
                                        ComprehensivePatterns::RCF r) {
  if (b) {
    return std::make_pair(r, r.cf_val);
  } else {
    return std::make_pair(std::move(r), 0u);
  }
}

__attribute__((pure)) unsigned int ComprehensivePatterns::match_with_wild(
    const std::optional<ComprehensivePatterns::RCF> &o) {
  if (o.has_value()) {
    const ComprehensivePatterns::RCF &r = *o;
    return r.cf_val;
  } else {
    return 0u;
  }
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::sum_with_state(const unsigned int &n,
                                      const ComprehensivePatterns::RCF &r) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    decltype((std::declval<const ComprehensivePatterns::RCF &>()).cf_val) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = r.cf_val;
      } else {
        unsigned int m = n - 1;
        _stack.emplace_back(_Call1{r.cf_val});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::even_count(const unsigned int &n,
                                  const ComprehensivePatterns::RCF &r) {
  if (n <= 0) {
    return 0u;
  } else {
    unsigned int m = n - 1;
    return (1u + odd_count(m, r));
  }
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::odd_count(const unsigned int &n,
                                 const ComprehensivePatterns::RCF &r) {
  if (n <= 0) {
    return r.cf_val;
  } else {
    unsigned int m = n - 1;
    return (1u + even_count(m, r));
  }
}

__attribute__((pure)) unsigned int ComprehensivePatterns::accum_with_state(
    const unsigned int &n, const ComprehensivePatterns::StateLB &s) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    decltype((std::declval<const ComprehensivePatterns::StateLB &>())
                 .lb_value) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = s.lb_value;
      } else {
        unsigned int m = n - 1;
        _stack.emplace_back(_Call1{s.lb_value});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

__attribute__((pure)) ComprehensivePatterns::StateOP
ComprehensivePatterns::identity(ComprehensivePatterns::StateOP s) {
  return s;
}

__attribute__((pure)) unsigned int ComprehensivePatterns::extract_via_match(
    const ComprehensivePatterns::StateOP &s) {
  return identity(s).op_value;
}

__attribute__((pure)) ComprehensivePatterns::StateOP
ComprehensivePatterns::consume_state(ComprehensivePatterns::StateOP s) {
  return s;
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::match_consumed(const ComprehensivePatterns::StateOP &s) {
  return consume_state(s).op_value;
}

__attribute__((pure)) std::pair<ComprehensivePatterns::StateOP, unsigned int>
ComprehensivePatterns::force_owned(ComprehensivePatterns::StateOP s) {
  unsigned int result = s.op_value;
  return std::make_pair(std::move(s), result);
}

__attribute__((pure)) std::pair<
    std::pair<ComprehensivePatterns::StateOP, ComprehensivePatterns::StateOP>,
    unsigned int>
ComprehensivePatterns::pair_then_match(ComprehensivePatterns::StateOP s) {
  std::pair<ComprehensivePatterns::StateOP, ComprehensivePatterns::StateOP> p =
      std::make_pair(s, s);
  unsigned int x = std::move(s).op_value;
  return std::make_pair(p, x);
}
