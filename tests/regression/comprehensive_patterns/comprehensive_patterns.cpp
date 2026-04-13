#include <comprehensive_patterns.h>

#include <any>
#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

__attribute__((pure))
std::pair<std::pair<std::shared_ptr<ComprehensivePatterns::S>, unsigned int>,
          unsigned int>
ComprehensivePatterns::syntactic_variation(
    std::shared_ptr<ComprehensivePatterns::S> s) {
  unsigned int a = s->s_a;
  std::function<unsigned int(std::shared_ptr<ComprehensivePatterns::S>)> b =
      [](const std::shared_ptr<ComprehensivePatterns::S> &s0) {
        return s0->s_b;
      };
  return std::make_pair(std::make_pair(s, a), b(s));
}

__attribute__((pure))
std::pair<std::shared_ptr<ComprehensivePatterns::S>, unsigned int>
ComprehensivePatterns::with_magic(std::shared_ptr<ComprehensivePatterns::S> s) {
  return std::make_pair(s, s->s_a);
}

__attribute__((pure)) std::pair<
    std::pair<
        std::pair<
            std::pair<
                std::pair<std::pair<std::shared_ptr<ComprehensivePatterns::L5>,
                                    std::shared_ptr<ComprehensivePatterns::L4>>,
                          std::shared_ptr<ComprehensivePatterns::L3>>,
                std::shared_ptr<ComprehensivePatterns::L2>>,
            std::shared_ptr<ComprehensivePatterns::L1>>,
        std::shared_ptr<ComprehensivePatterns::S>>,
    unsigned int>
ComprehensivePatterns::deep_nest(
    std::shared_ptr<ComprehensivePatterns::L5> l5) {
  std::shared_ptr<ComprehensivePatterns::L4> l4 = l5->l5_l4;
  std::shared_ptr<ComprehensivePatterns::L3> l3 = l4->l4_l3;
  std::shared_ptr<ComprehensivePatterns::L2> l2 = l3->l3_l2;
  std::shared_ptr<ComprehensivePatterns::L1> l1 = l2->l2_l1;
  std::shared_ptr<ComprehensivePatterns::S> s = l1->l1_s;
  return std::make_pair(
      std::make_pair(
          std::make_pair(
              std::make_pair(
                  std::make_pair(std::make_pair(std::move(l5), std::move(l4)),
                                 std::move(l3)),
                  std::move(l2)),
              std::move(l1)),
          s),
      s->s_a);
}

__attribute__((pure))
std::pair<std::pair<std::pair<std::shared_ptr<ComprehensivePatterns::S>,
                              unsigned int>,
                    unsigned int>,
          unsigned int>
ComprehensivePatterns::nested_pair_reuse(
    std::shared_ptr<ComprehensivePatterns::S> s) {
  return std::make_pair(std::make_pair(std::make_pair(s, s->s_a), s->s_b),
                        s->s_c);
}

__attribute__((pure))
std::pair<std::shared_ptr<ComprehensivePatterns::S>, unsigned int>
ComprehensivePatterns::compose(std::shared_ptr<ComprehensivePatterns::S> s) {
  std::function<unsigned int(std::shared_ptr<ComprehensivePatterns::S>)> f =
      [](const std::shared_ptr<ComprehensivePatterns::S> &x) { return x->s_a; };
  return std::make_pair(s, f(s));
}

__attribute__((pure)) std::pair<std::function<unsigned int(unsigned int)>,
                                std::shared_ptr<ComprehensivePatterns::S>>
ComprehensivePatterns::lambda_proj(
    std::shared_ptr<ComprehensivePatterns::S> s) {
  return std::make_pair([=](const unsigned int) mutable { return s->s_a; }, s);
}

__attribute__((pure))
std::pair<std::pair<std::pair<std::shared_ptr<ComprehensivePatterns::S>,
                              unsigned int>,
                    unsigned int>,
          unsigned int>
ComprehensivePatterns::proj_chain(std::shared_ptr<ComprehensivePatterns::S> s) {
  unsigned int a = s->s_a;
  unsigned int b = s->s_b;
  unsigned int c = s->s_c;
  return std::make_pair(std::make_pair(std::make_pair(std::move(s), a), b), c);
}

__attribute__((pure))
std::pair<std::pair<std::pair<std::shared_ptr<ComprehensivePatterns::S>,
                              std::shared_ptr<ComprehensivePatterns::S>>,
                    std::pair<unsigned int, unsigned int>>,
          std::pair<std::pair<unsigned int, unsigned int>,
                    std::pair<unsigned int, unsigned int>>>
ComprehensivePatterns::octuple(std::shared_ptr<ComprehensivePatterns::S> s) {
  return std::make_pair(
      std::make_pair(std::make_pair(s, s), std::make_pair(s->s_a, s->s_b)),
      std::make_pair(std::make_pair(s->s_c, s->s_a),
                     std::make_pair(s->s_b, s->s_c)));
}

__attribute__((pure))
std::pair<std::optional<std::pair<std::shared_ptr<ComprehensivePatterns::S>,
                                  unsigned int>>,
          std::shared_ptr<ComprehensivePatterns::S>>
ComprehensivePatterns::nested_containers(
    std::shared_ptr<ComprehensivePatterns::S> s) {
  return std::make_pair(
      std::make_optional<
          std::pair<std::shared_ptr<ComprehensivePatterns::S>, unsigned int>>(
          std::make_pair(s, s->s_a)),
      s);
}

__attribute__((pure))
std::pair<std::pair<std::shared_ptr<ComprehensivePatterns::S>, unsigned int>,
          unsigned int>
ComprehensivePatterns::match_pair(
    const std::pair<std::shared_ptr<ComprehensivePatterns::S>, unsigned int>
        p) {
  const std::shared_ptr<ComprehensivePatterns::S> &s = p.first;
  const unsigned int &n = p.second;
  return std::make_pair(std::make_pair(s, n), s->s_a);
}

std::shared_ptr<
    List<std::pair<std::shared_ptr<ComprehensivePatterns::S>, unsigned int>>>
ComprehensivePatterns::make_list(const unsigned int n,
                                 std::shared_ptr<ComprehensivePatterns::S> s) {
  std::shared_ptr<
      List<std::pair<std::shared_ptr<ComprehensivePatterns::S>, unsigned int>>>
      _head{};
  std::shared_ptr<
      List<std::pair<std::shared_ptr<ComprehensivePatterns::S>, unsigned int>>>
      _last{};
  unsigned int _loop_n = n;
  bool _continue = true;
  while (_continue) {
    if (_loop_n <= 0) {
      {
        if (_last) {
          std::get<typename List<std::pair<
              std::shared_ptr<ComprehensivePatterns::S>, unsigned int>>::Cons>(
              _last->v_mut())
              .d_a1 = List<std::pair<std::shared_ptr<ComprehensivePatterns::S>,
                                     unsigned int>>::nil();
        } else {
          _head = List<std::pair<std::shared_ptr<ComprehensivePatterns::S>,
                                 unsigned int>>::nil();
        }
        _continue = false;
      }
    } else {
      unsigned int m = _loop_n - 1;
      {
        auto _cell =
            List<std::pair<std::shared_ptr<ComprehensivePatterns::S>,
                           unsigned int>>::cons(std::make_pair(s, s->s_a),
                                                nullptr);
        if (_last) {
          std::get<typename List<std::pair<
              std::shared_ptr<ComprehensivePatterns::S>, unsigned int>>::Cons>(
              _last->v_mut())
              .d_a1 = _cell;
        } else {
          _head = _cell;
        }
        _last = _cell;
        _loop_n = m;
        continue;
      }
    }
  }
  return _head;
}

__attribute__((pure))
std::optional<std::pair<std::shared_ptr<ComprehensivePatterns::S>,
                        std::shared_ptr<ComprehensivePatterns::S>>>
ComprehensivePatterns::multi_match(
    const std::optional<std::shared_ptr<ComprehensivePatterns::S>> o1,
    const std::optional<std::shared_ptr<ComprehensivePatterns::S>> o2) {
  if (o1.has_value()) {
    const std::shared_ptr<ComprehensivePatterns::S> &s1 = *o1;
    if (o2.has_value()) {
      const std::shared_ptr<ComprehensivePatterns::S> &_x = *o2;
      return std::make_optional<
          std::pair<std::shared_ptr<ComprehensivePatterns::S>,
                    std::shared_ptr<ComprehensivePatterns::S>>>(
          std::make_pair(s1, s1));
    } else {
      return std::make_optional<
          std::pair<std::shared_ptr<ComprehensivePatterns::S>,
                    std::shared_ptr<ComprehensivePatterns::S>>>(
          std::make_pair(s1, s1));
    }
  } else {
    return std::optional<
        std::pair<std::shared_ptr<ComprehensivePatterns::S>,
                  std::shared_ptr<ComprehensivePatterns::S>>>();
  }
}

__attribute__((pure))
std::pair<std::shared_ptr<ComprehensivePatterns::S>, unsigned int>
ComprehensivePatterns::match_three(
    const ComprehensivePatterns::Three t,
    std::shared_ptr<ComprehensivePatterns::S> s) {
  switch (t) {
  case Three::e_A: {
    return std::make_pair(s, s->s_a);
  }
  case Three::e_B: {
    return std::make_pair(s, s->s_b);
  }
  case Three::e_C: {
    return std::make_pair(s, s->s_c);
  }
  default:
    std::unreachable();
  }
}

__attribute__((pure))
std::pair<std::shared_ptr<ComprehensivePatterns::S>, unsigned int>
ComprehensivePatterns::let_in_arg(std::shared_ptr<ComprehensivePatterns::S> s) {
  return std::make_pair(s, s->s_a);
}

__attribute__((pure))
std::pair<std::shared_ptr<ComprehensivePatterns::S>, unsigned int>
ComprehensivePatterns::match_record(
    std::shared_ptr<ComprehensivePatterns::S> s) {
  unsigned int a = s->s_a;
  std::any _x = s->s_b;
  std::any _x0 = s->s_c;
  return std::make_pair(s, a);
}

__attribute__((pure))
std::pair<std::shared_ptr<ComprehensivePatterns::S>, unsigned int>
ComprehensivePatterns::rebind(std::shared_ptr<ComprehensivePatterns::S> s1) {
  return std::make_pair(s1, s1->s_a);
}

__attribute__((pure)) std::pair<std::function<unsigned int(std::monostate)>,
                                std::function<unsigned int(std::monostate)>>
ComprehensivePatterns::closure_pair(
    std::shared_ptr<ComprehensivePatterns::S> s) {
  return std::make_pair([=](const std::monostate) mutable { return s->s_a; },
                        [=](const std::monostate) mutable { return s->s_b; });
}

std::shared_ptr<Sig<std::shared_ptr<ComprehensivePatterns::S>>>
ComprehensivePatterns::sigma_reuse(
    std::shared_ptr<ComprehensivePatterns::S> s) {
  return Sig<std::shared_ptr<ComprehensivePatterns::S>>::exist(s);
}

__attribute__((pure))
std::pair<unsigned int, std::pair<unsigned int, unsigned int>>
ComprehensivePatterns::multi_proj_arg(
    const std::shared_ptr<ComprehensivePatterns::S> &s) {
  return std::make_pair(s->s_a, std::make_pair(s->s_a, s->s_b));
}

__attribute__((pure)) std::pair<std::shared_ptr<ComprehensivePatterns::Either>,
                                std::shared_ptr<ComprehensivePatterns::Either>>
ComprehensivePatterns::both_in_sum(
    std::shared_ptr<ComprehensivePatterns::S> s) {
  return std::make_pair(Either::left_s(s), Either::right_n(s->s_a));
}

__attribute__((pure))
std::pair<std::pair<std::pair<std::shared_ptr<ComprehensivePatterns::R3>,
                              std::shared_ptr<ComprehensivePatterns::R2>>,
                    std::shared_ptr<ComprehensivePatterns::R1>>,
          unsigned int>
ComprehensivePatterns::hard_proj_chain(
    std::shared_ptr<ComprehensivePatterns::R3> r3) {
  std::shared_ptr<ComprehensivePatterns::R2> r2 = r3->r3_r2;
  std::shared_ptr<ComprehensivePatterns::R1> r1 = r2->r2_inner;
  return std::make_pair(
      std::make_pair(std::make_pair(std::move(r3), std::move(r2)), r1),
      r1->r1_val);
}

__attribute__((pure))
std::pair<std::pair<std::shared_ptr<ComprehensivePatterns::R2>,
                    std::shared_ptr<ComprehensivePatterns::R1>>,
          unsigned int>
ComprehensivePatterns::multi_path(
    const std::shared_ptr<ComprehensivePatterns::R3> &r3) {
  return std::make_pair(std::make_pair(r3->r3_r2, r3->r3_r2->r2_inner),
                        r3->r3_r2->r2_inner->r1_val);
}

__attribute__((pure))
std::pair<std::pair<std::shared_ptr<ComprehensivePatterns::R2>,
                    std::shared_ptr<ComprehensivePatterns::R1>>,
          unsigned int>
ComprehensivePatterns::let_proj(std::shared_ptr<ComprehensivePatterns::R2> r2) {
  std::shared_ptr<ComprehensivePatterns::R1> r1 = r2->r2_inner;
  unsigned int n = r1->r1_val;
  return std::make_pair(std::make_pair(std::move(r2), std::move(r1)), n);
}

__attribute__((pure)) unsigned int ComprehensivePatterns::extract_val(
    const std::shared_ptr<ComprehensivePatterns::R1> &r1) {
  return r1->r1_val;
}

__attribute__((pure))
std::pair<std::shared_ptr<ComprehensivePatterns::R2>, unsigned int>
ComprehensivePatterns::nested_call(
    std::shared_ptr<ComprehensivePatterns::R2> r2) {
  return std::make_pair(r2, extract_val(r2->r2_inner));
}

__attribute__((pure))
std::pair<std::pair<std::shared_ptr<ComprehensivePatterns::R2>,
                    std::shared_ptr<ComprehensivePatterns::R1>>,
          unsigned int>
ComprehensivePatterns::multi_proj_let(const unsigned int n) {
  std::shared_ptr<ComprehensivePatterns::R2> r2 =
      std::make_shared<ComprehensivePatterns::R2>(
          R2{std::make_shared<ComprehensivePatterns::R1>(R1{n}), n});
  return std::make_pair(std::make_pair(r2, r2->r2_inner), r2->r2_data);
}

__attribute__((pure))
std::optional<std::pair<std::shared_ptr<ComprehensivePatterns::R2>,
                        std::shared_ptr<ComprehensivePatterns::R1>>>
ComprehensivePatterns::match_proj(
    std::shared_ptr<ComprehensivePatterns::R2> r2) {
  std::shared_ptr<ComprehensivePatterns::R1> r1 = r2->r2_inner;
  return std::make_optional<
      std::pair<std::shared_ptr<ComprehensivePatterns::R2>,
                std::shared_ptr<ComprehensivePatterns::R1>>>(
      std::make_pair(std::move(r2), std::move(r1)));
}

__attribute__((pure))
std::pair<std::pair<std::shared_ptr<ComprehensivePatterns::R1>, unsigned int>,
          unsigned int>
ComprehensivePatterns::proj_multi_use(
    const std::shared_ptr<ComprehensivePatterns::R2> &r2) {
  const std::shared_ptr<ComprehensivePatterns::R1> &r1 = r2->r2_inner;
  return std::make_pair(std::make_pair(r1, r1->r1_val), r1->r1_val);
}

__attribute__((pure))
std::pair<std::pair<std::shared_ptr<ComprehensivePatterns::R3>,
                    std::shared_ptr<ComprehensivePatterns::R2>>,
          std::pair<std::shared_ptr<ComprehensivePatterns::R1>, unsigned int>>
ComprehensivePatterns::complex_nest(
    std::shared_ptr<ComprehensivePatterns::R3> r3) {
  return std::make_pair(
      std::make_pair(r3, r3->r3_r2),
      std::make_pair(r3->r3_r2->r2_inner, r3->r3_r2->r2_inner->r1_val));
}

std::shared_ptr<ComprehensivePatterns::R2>
ComprehensivePatterns::make_r2(const unsigned int n) {
  return std::make_shared<ComprehensivePatterns::R2>(
      R2{std::make_shared<ComprehensivePatterns::R1>(R1{n}), n});
}

__attribute__((pure))
std::pair<std::pair<std::shared_ptr<ComprehensivePatterns::R2>,
                    std::shared_ptr<ComprehensivePatterns::R1>>,
          unsigned int>
ComprehensivePatterns::from_func(const unsigned int n) {
  std::shared_ptr<ComprehensivePatterns::R2> r2 = make_r2(n);
  return std::make_pair(std::make_pair(r2, r2->r2_inner), r2->r2_data);
}

__attribute__((pure))
std::pair<std::pair<std::shared_ptr<ComprehensivePatterns::R2>,
                    std::shared_ptr<ComprehensivePatterns::R1>>,
          std::pair<std::shared_ptr<ComprehensivePatterns::R1>, unsigned int>>
ComprehensivePatterns::pair_of_pairs(
    std::shared_ptr<ComprehensivePatterns::R2> r2) {
  std::shared_ptr<ComprehensivePatterns::R1> r1 = r2->r2_inner;
  return std::make_pair(std::make_pair(std::move(r2), r1),
                        std::make_pair(r1, r1->r1_val));
}

__attribute__((pure)) std::pair<std::shared_ptr<ComprehensivePatterns::R2>,
                                std::shared_ptr<ComprehensivePatterns::R1>>
ComprehensivePatterns::cond_proj(
    const bool b, std::shared_ptr<ComprehensivePatterns::R2> r2) {
  if (b) {
    return std::make_pair(r2, r2->r2_inner);
  } else {
    return std::make_pair(r2, r2->r2_inner);
  }
}

std::shared_ptr<List<std::pair<std::shared_ptr<ComprehensivePatterns::R2>,
                               std::shared_ptr<ComprehensivePatterns::R1>>>>
ComprehensivePatterns::repeat_r2(
    const unsigned int n, std::shared_ptr<ComprehensivePatterns::R2> r2) {
  std::shared_ptr<List<std::pair<std::shared_ptr<ComprehensivePatterns::R2>,
                                 std::shared_ptr<ComprehensivePatterns::R1>>>>
      _head{};
  std::shared_ptr<List<std::pair<std::shared_ptr<ComprehensivePatterns::R2>,
                                 std::shared_ptr<ComprehensivePatterns::R1>>>>
      _last{};
  unsigned int _loop_n = n;
  bool _continue = true;
  while (_continue) {
    if (_loop_n <= 0) {
      {
        if (_last) {
          std::get<typename List<
              std::pair<std::shared_ptr<ComprehensivePatterns::R2>,
                        std::shared_ptr<ComprehensivePatterns::R1>>>::Cons>(
              _last->v_mut())
              .d_a1 = List<
              std::pair<std::shared_ptr<ComprehensivePatterns::R2>,
                        std::shared_ptr<ComprehensivePatterns::R1>>>::nil();
        } else {
          _head = List<
              std::pair<std::shared_ptr<ComprehensivePatterns::R2>,
                        std::shared_ptr<ComprehensivePatterns::R1>>>::nil();
        }
        _continue = false;
      }
    } else {
      unsigned int m = _loop_n - 1;
      {
        auto _cell =
            List<std::pair<std::shared_ptr<ComprehensivePatterns::R2>,
                           std::shared_ptr<ComprehensivePatterns::R1>>>::
                cons(std::make_pair(r2, r2->r2_inner), nullptr);
        if (_last) {
          std::get<typename List<
              std::pair<std::shared_ptr<ComprehensivePatterns::R2>,
                        std::shared_ptr<ComprehensivePatterns::R1>>>::Cons>(
              _last->v_mut())
              .d_a1 = _cell;
        } else {
          _head = _cell;
        }
        _last = _cell;
        _loop_n = m;
        continue;
      }
    }
  }
  return _head;
}

__attribute__((pure))
std::pair<std::pair<std::shared_ptr<ComprehensivePatterns::R3>,
                    std::shared_ptr<ComprehensivePatterns::R2>>,
          std::shared_ptr<ComprehensivePatterns::R1>>
ComprehensivePatterns::nested_lets(
    std::shared_ptr<ComprehensivePatterns::R3> r3) {
  std::shared_ptr<ComprehensivePatterns::R2> r2 = r3->r3_r2;
  std::shared_ptr<ComprehensivePatterns::R1> r1 = r2->r2_inner;
  return std::make_pair(std::make_pair(std::move(r3), std::move(r2)),
                        std::move(r1));
}

__attribute__((pure))
std::pair<std::shared_ptr<ComprehensivePatterns::R1>, unsigned int>
ComprehensivePatterns::double_proj(
    const std::shared_ptr<ComprehensivePatterns::R3> &r3) {
  return std::make_pair(r3->r3_r2->r2_inner, r3->r3_r2->r2_inner->r1_val);
}

__attribute__((pure))
std::pair<std::pair<std::shared_ptr<ComprehensivePatterns::R3>,
                    std::shared_ptr<ComprehensivePatterns::R2>>,
          std::shared_ptr<ComprehensivePatterns::R2>>
ComprehensivePatterns::mixed_access(
    std::shared_ptr<ComprehensivePatterns::R3> r3) {
  std::shared_ptr<ComprehensivePatterns::R2> r2 = r3->r3_r2;
  return std::make_pair(std::make_pair(r3, std::move(r2)), r3->r3_r2);
}

__attribute__((pure)) std::pair<std::shared_ptr<ComprehensivePatterns::R2>,
                                std::shared_ptr<ComprehensivePatterns::R1>>
ComprehensivePatterns::return_proj_h(
    std::shared_ptr<ComprehensivePatterns::R2> r2) {
  return std::make_pair(r2, r2->r2_inner);
}

__attribute__((pure))
std::pair<std::pair<std::pair<std::shared_ptr<ComprehensivePatterns::R3>,
                              std::shared_ptr<ComprehensivePatterns::R2>>,
                    std::shared_ptr<ComprehensivePatterns::R1>>,
          unsigned int>
ComprehensivePatterns::all_levels(
    std::shared_ptr<ComprehensivePatterns::R3> r3) {
  return std::make_pair(
      std::make_pair(std::make_pair(r3, r3->r3_r2), r3->r3_r2->r2_inner),
      r3->r3_r2->r2_inner->r1_val);
}

__attribute__((pure)) std::pair<std::shared_ptr<ComprehensivePatterns::R1>,
                                std::shared_ptr<ComprehensivePatterns::R1>>
ComprehensivePatterns::let_and_proj(
    const std::shared_ptr<ComprehensivePatterns::R2> &r2) {
  const std::shared_ptr<ComprehensivePatterns::R1> &r1 = r2->r2_inner;
  return std::make_pair(r1, r2->r2_inner);
}

__attribute__((pure)) std::pair<std::shared_ptr<ComprehensivePatterns::R2>,
                                std::shared_ptr<ComprehensivePatterns::R2>>
ComprehensivePatterns::multi_construct(
    std::shared_ptr<ComprehensivePatterns::R1> r1) {
  std::shared_ptr<ComprehensivePatterns::R2> r2a =
      std::make_shared<ComprehensivePatterns::R2>(R2{r1, 0u});
  std::shared_ptr<ComprehensivePatterns::R2> r2b =
      std::make_shared<ComprehensivePatterns::R2>(R2{r1, 1u});
  return std::make_pair(std::move(r2a), std::move(r2b));
}

__attribute__((pure))
std::optional<std::pair<std::shared_ptr<ComprehensivePatterns::R2>,
                        std::shared_ptr<ComprehensivePatterns::R1>>>
ComprehensivePatterns::option_proj(
    const std::optional<std::shared_ptr<ComprehensivePatterns::R2>> o) {
  if (o.has_value()) {
    const std::shared_ptr<ComprehensivePatterns::R2> &r2 = *o;
    return std::make_optional<
        std::pair<std::shared_ptr<ComprehensivePatterns::R2>,
                  std::shared_ptr<ComprehensivePatterns::R1>>>(
        std::make_pair(r2, r2->r2_inner));
  } else {
    return std::optional<
        std::pair<std::shared_ptr<ComprehensivePatterns::R2>,
                  std::shared_ptr<ComprehensivePatterns::R1>>>();
  }
}

__attribute__((pure))
std::pair<std::shared_ptr<ComprehensivePatterns::R>, unsigned int>
ComprehensivePatterns::pair_inline_proj(
    std::shared_ptr<ComprehensivePatterns::R> r) {
  return std::make_pair(r, r->val);
}

__attribute__((pure))
std::pair<std::pair<std::shared_ptr<ComprehensivePatterns::R>, unsigned int>,
          unsigned int>
ComprehensivePatterns::nested_pair_inline(
    std::shared_ptr<ComprehensivePatterns::R> r) {
  return std::make_pair(std::make_pair(r, r->val), r->dat);
}

__attribute__((pure)) unsigned int ComprehensivePatterns::match_bind_and_use(
    const std::shared_ptr<ComprehensivePatterns::R> &r) {
  unsigned int v = r->val;
  unsigned int d = r->dat;
  return ((v + d) + r->val);
}

__attribute__((pure)) unsigned int ComprehensivePatterns::let_with_type(
    const std::shared_ptr<ComprehensivePatterns::R> &r) {
  return (r->val + r->val);
}

__attribute__((pure)) unsigned int ComprehensivePatterns::proj_of_last_use(
    const std::shared_ptr<ComprehensivePatterns::R> &r1) {
  return r1->val;
}

__attribute__((pure)) unsigned int ComprehensivePatterns::multi_let_same(
    const std::shared_ptr<ComprehensivePatterns::R> &r) {
  return ((r->val + r->val) + r->val);
}

__attribute__((pure)) unsigned int ComprehensivePatterns::option_unwrap_proj(
    const std::optional<std::shared_ptr<ComprehensivePatterns::R>> o) {
  if (o.has_value()) {
    const std::shared_ptr<ComprehensivePatterns::R> &r = *o;
    return (r->val + r->dat);
  } else {
    return 0u;
  }
}

__attribute__((pure))
std::pair<std::shared_ptr<ComprehensivePatterns::R>, unsigned int>
ComprehensivePatterns::fun_result_and_proj(const unsigned int n) {
  std::shared_ptr<ComprehensivePatterns::R> r =
      std::make_shared<ComprehensivePatterns::R>(R{n, n});
  return std::make_pair(r, r->val);
}

__attribute__((pure)) std::optional<unsigned int>
ComprehensivePatterns::match_multi_use(
    const std::optional<std::shared_ptr<ComprehensivePatterns::R>> o) {
  if (o.has_value()) {
    const std::shared_ptr<ComprehensivePatterns::R> &r = *o;
    return std::make_optional<unsigned int>((r->val + r->dat));
  } else {
    return std::optional<unsigned int>();
  }
}

__attribute__((pure))
std::pair<std::pair<std::shared_ptr<ComprehensivePatterns::R>, unsigned int>,
          unsigned int>
ComprehensivePatterns::tuple_proj(std::shared_ptr<ComprehensivePatterns::R> r) {
  return std::make_pair(std::make_pair(r, r->val), r->dat);
}

__attribute__((pure))
std::pair<std::shared_ptr<ComprehensivePatterns::R>, unsigned int>
ComprehensivePatterns::chain_to_pair(
    std::shared_ptr<ComprehensivePatterns::R> r1) {
  return std::make_pair(r1, r1->val);
}

std::shared_ptr<
    List<std::pair<std::shared_ptr<ComprehensivePatterns::R>, unsigned int>>>
ComprehensivePatterns::repeat_pair(
    const unsigned int n, std::shared_ptr<ComprehensivePatterns::R> r) {
  std::shared_ptr<
      List<std::pair<std::shared_ptr<ComprehensivePatterns::R>, unsigned int>>>
      _head{};
  std::shared_ptr<
      List<std::pair<std::shared_ptr<ComprehensivePatterns::R>, unsigned int>>>
      _last{};
  unsigned int _loop_n = n;
  bool _continue = true;
  while (_continue) {
    if (_loop_n <= 0) {
      {
        if (_last) {
          std::get<typename List<std::pair<
              std::shared_ptr<ComprehensivePatterns::R>, unsigned int>>::Cons>(
              _last->v_mut())
              .d_a1 = List<std::pair<std::shared_ptr<ComprehensivePatterns::R>,
                                     unsigned int>>::nil();
        } else {
          _head = List<std::pair<std::shared_ptr<ComprehensivePatterns::R>,
                                 unsigned int>>::nil();
        }
        _continue = false;
      }
    } else {
      unsigned int m = _loop_n - 1;
      {
        auto _cell =
            List<std::pair<std::shared_ptr<ComprehensivePatterns::R>,
                           unsigned int>>::cons(std::make_pair(r, r->val),
                                                nullptr);
        if (_last) {
          std::get<typename List<std::pair<
              std::shared_ptr<ComprehensivePatterns::R>, unsigned int>>::Cons>(
              _last->v_mut())
              .d_a1 = _cell;
        } else {
          _head = _cell;
        }
        _last = _cell;
        _loop_n = m;
        continue;
      }
    }
  }
  return _head;
}

__attribute__((pure))
std::pair<std::shared_ptr<ComprehensivePatterns::R>, unsigned int>
ComprehensivePatterns::cond_pair(const bool b,
                                 std::shared_ptr<ComprehensivePatterns::R> r) {
  if (b) {
    return std::make_pair(r, r->val);
  } else {
    return std::make_pair(r, r->dat);
  }
}

__attribute__((pure)) unsigned int ComprehensivePatterns::nested_match(
    const std::optional<std::shared_ptr<ComprehensivePatterns::R>> o1,
    const std::optional<std::shared_ptr<ComprehensivePatterns::R>> o2) {
  if (o1.has_value()) {
    const std::shared_ptr<ComprehensivePatterns::R> &r1 = *o1;
    if (o2.has_value()) {
      const std::shared_ptr<ComprehensivePatterns::R> &r2 = *o2;
      return (r1->val + r2->val);
    } else {
      return r1->val;
    }
  } else {
    return 0u;
  }
}

__attribute__((pure)) std::pair<unsigned int, unsigned int>
ComprehensivePatterns::both_proj(
    const std::shared_ptr<ComprehensivePatterns::R> &r) {
  return std::make_pair(r->val, r->dat);
}

__attribute__((pure)) unsigned int ComprehensivePatterns::compose_proj(
    const std::shared_ptr<ComprehensivePatterns::R> &r) {
  std::function<unsigned int(std::shared_ptr<ComprehensivePatterns::R>)> f =
      [](const std::shared_ptr<ComprehensivePatterns::R> &x) { return x->val; };
  std::function<unsigned int(std::shared_ptr<ComprehensivePatterns::R>)> g =
      [](const std::shared_ptr<ComprehensivePatterns::R> &x) { return x->dat; };
  return (f(r) + g(r));
}

__attribute__((pure)) std::optional<unsigned int>
ComprehensivePatterns::proj_through_option(
    const std::shared_ptr<ComprehensivePatterns::R> &r) {
  return std::make_optional<unsigned int>(r->val);
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::use_proj(const unsigned int n) {
  return n;
}

__attribute__((pure)) unsigned int ComprehensivePatterns::proj_as_arg(
    const std::shared_ptr<ComprehensivePatterns::NC> &r) {
  return use_proj(r->nc_a);
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::use_two(const unsigned int _x0, const unsigned int _x1) {
  return (_x0 + _x1);
}

__attribute__((pure)) unsigned int ComprehensivePatterns::multi_proj_args(
    const std::shared_ptr<ComprehensivePatterns::NC> &r) {
  return use_two(r->nc_a, r->nc_b);
}

__attribute__((pure)) unsigned int ComprehensivePatterns::let_proj_then_base(
    const std::shared_ptr<ComprehensivePatterns::NC> &r) {
  unsigned int x = r->nc_a;
  unsigned int y = r->nc_b;
  return (x + y);
}

__attribute__((pure)) unsigned int ComprehensivePatterns::base_then_multi_proj(
    const std::shared_ptr<ComprehensivePatterns::NC> &r) {
  return ((r->nc_a + r->nc_b) + r->nc_c);
}

__attribute__((pure)) unsigned int ComprehensivePatterns::proj_in_condition(
    const std::shared_ptr<ComprehensivePatterns::NC> &r) {
  if (r->nc_a == 0u) {
    return r->nc_b;
  } else {
    return r->nc_c;
  }
}

__attribute__((pure)) unsigned int ComprehensivePatterns::proj_in_scrutinee(
    const std::shared_ptr<ComprehensivePatterns::NC> &r) {
  if (r->nc_a <= 0) {
    return r->nc_b;
  } else {
    unsigned int n = r->nc_a - 1;
    return (n + r->nc_c);
  }
}

__attribute__((pure)) unsigned int ComprehensivePatterns::return_proj_nc(
    const std::shared_ptr<ComprehensivePatterns::NC> &r) {
  return r->nc_a;
}

__attribute__((pure)) unsigned int ComprehensivePatterns::call_return_proj(
    const std::shared_ptr<ComprehensivePatterns::NC> &r) {
  return (return_proj_nc(r) + r->nc_b);
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::inc(const unsigned int n) {
  return (n + 1u);
}

__attribute__((pure)) unsigned int ComprehensivePatterns::nested_proj_calls(
    const std::shared_ptr<ComprehensivePatterns::NC> &r) {
  return (inc(r->nc_a) + inc(r->nc_b));
}

__attribute__((pure)) unsigned int ComprehensivePatterns::count_down(
    const unsigned int n, const std::shared_ptr<ComprehensivePatterns::NC> &r) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    decltype(std::declval<const std::shared_ptr<ComprehensivePatterns::NC> &>()
                 ->nc_b) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            const unsigned int n = _f.n;
                            if (n <= 0) {
                              _result = r->nc_a;
                            } else {
                              unsigned int m = n - 1;
                              _stack.emplace_back(_Call1{r->nc_b});
                              _stack.emplace_back(_Enter{m});
                            }
                          },
                          [&](_Call1 _f) { _result = (_result + _f._s0); }},
               _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::f1(const std::shared_ptr<ComprehensivePatterns::NC> &r) {
  return r->nc_a;
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::f2(const std::shared_ptr<ComprehensivePatterns::NC> &r) {
  return r->nc_b;
}

__attribute__((pure)) unsigned int ComprehensivePatterns::multi_function_calls(
    const std::shared_ptr<ComprehensivePatterns::NC> &r) {
  return (f1(r) + f2(r));
}

__attribute__((pure)) unsigned int ComprehensivePatterns::proj_then_match(
    const std::shared_ptr<ComprehensivePatterns::NC> &r) {
  unsigned int x = r->nc_a;
  std::any _x = r->nc_a;
  unsigned int b = r->nc_b;
  std::any _x0 = r->nc_c;
  return (x + b);
}

__attribute__((pure)) unsigned int ComprehensivePatterns::let_used_twice(
    const std::shared_ptr<ComprehensivePatterns::NC> &r) {
  unsigned int x = r->nc_a;
  return (x + x);
}

__attribute__((pure)) bool ComprehensivePatterns::base_in_call_and_proj(
    const std::shared_ptr<ComprehensivePatterns::NC> &r) {
  return r->nc_a == r->nc_a;
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::chained_lets_same_base(
    const std::shared_ptr<ComprehensivePatterns::NC> &r) {
  unsigned int x = r->nc_a;
  unsigned int y = r->nc_b;
  unsigned int z = r->nc_c;
  return ((x + y) + z);
}

__attribute__((pure)) unsigned int ComprehensivePatterns::double_proj_nc(
    const std::shared_ptr<ComprehensivePatterns::OuterNC> &o) {
  return (o->outer_nc->nc_a + o->outer_nc->nc_b);
}

__attribute__((pure)) unsigned int ComprehensivePatterns::multi_positions(
    const std::shared_ptr<ComprehensivePatterns::NC> &r) {
  return (r->nc_a + [&]() -> unsigned int {
    if (r->nc_b == 0u) {
      return r->nc_a;
    } else {
      return r->nc_c;
    }
  }());
}

__attribute__((pure)) unsigned int ComprehensivePatterns::sum_proj(
    const unsigned int n, const std::shared_ptr<ComprehensivePatterns::NC> &r) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    decltype(std::declval<const std::shared_ptr<ComprehensivePatterns::NC> &>()
                 ->nc_a) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            const unsigned int n = _f.n;
                            if (n <= 0) {
                              _result = 0u;
                            } else {
                              unsigned int m = n - 1;
                              _stack.emplace_back(_Call1{r->nc_a});
                              _stack.emplace_back(_Enter{m});
                            }
                          },
                          [&](_Call1 _f) { _result = (_f._s0 + _result); }},
               _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int ComprehensivePatterns::hof_test(
    const std::shared_ptr<ComprehensivePatterns::NC> &r) {
  return apply(
      [](const std::shared_ptr<ComprehensivePatterns::NC> &x) {
        return (x->nc_a + x->nc_b);
      },
      r);
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::use_two_fc(const unsigned int _x0,
                                  const unsigned int _x1) {
  return (_x0 + _x1);
}

__attribute__((pure)) unsigned int ComprehensivePatterns::bug_two_args(
    const std::shared_ptr<ComprehensivePatterns::State> &s) {
  return use_two_fc(s->state_value, s->state_data);
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::use_three(const unsigned int x, const unsigned int y,
                                 const unsigned int z) {
  return ((x + y) + z);
}

__attribute__((pure)) unsigned int ComprehensivePatterns::bug_three_args(
    const std::shared_ptr<ComprehensivePatterns::State> &s) {
  return use_three(s->state_value, s->state_data, s->state_value);
}

__attribute__((pure)) unsigned int ComprehensivePatterns::take_state_and_val(
    const std::shared_ptr<ComprehensivePatterns::State> &,
    const unsigned int n) {
  return n;
}

__attribute__((pure)) unsigned int ComprehensivePatterns::bug_state_and_proj(
    const std::shared_ptr<ComprehensivePatterns::State> &s) {
  return take_state_and_val(s, s->state_value);
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::inner_func(const unsigned int n) {
  return (n + 1u);
}

__attribute__((pure)) unsigned int ComprehensivePatterns::bug_nested_calls(
    const std::shared_ptr<ComprehensivePatterns::State> &s) {
  return use_two_fc(inner_func(s->state_value), inner_func(s->state_data));
}

__attribute__((pure)) unsigned int ComprehensivePatterns::bug_in_condition(
    const std::shared_ptr<ComprehensivePatterns::State> &s) {
  if (s->state_value == 0u) {
    return s->state_data;
  } else {
    return s->state_value;
  }
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::f1_fc(const unsigned int n) {
  return n;
}

__attribute__((pure)) unsigned int
ComprehensivePatterns::f2_fc(const unsigned int n) {
  return (n + 1u);
}

__attribute__((pure)) unsigned int ComprehensivePatterns::bug_multi_calls(
    const std::shared_ptr<ComprehensivePatterns::State> &s) {
  unsigned int v = s->state_value;
  return (f1_fc(v) + f2_fc(v));
}

__attribute__((pure))
std::pair<std::shared_ptr<ComprehensivePatterns::State>, unsigned int>
ComprehensivePatterns::bug_base_and_proj(
    const std::shared_ptr<ComprehensivePatterns::State> &s) {
  std::shared_ptr<ComprehensivePatterns::State> s2 =
      _bug_base_and_proj_consume(s);
  return std::make_pair(s2, s2->state_value);
}

__attribute__((pure)) unsigned int ComprehensivePatterns::sequential_lets(
    const std::shared_ptr<ComprehensivePatterns::State> &s) {
  return s->state_value;
}

__attribute__((pure))
std::pair<std::shared_ptr<ComprehensivePatterns::State>, unsigned int>
ComprehensivePatterns::let_then_use_base(
    std::shared_ptr<ComprehensivePatterns::State> s) {
  unsigned int v = s->state_value;
  return std::make_pair(std::move(s), v);
}

__attribute__((pure)) unsigned int ComprehensivePatterns::two_proj_sequence(
    const std::shared_ptr<ComprehensivePatterns::State> &s) {
  unsigned int v = s->state_value;
  unsigned int d = s->state_data;
  return (v + d);
}

__attribute__((pure)) unsigned int ComprehensivePatterns::let_multi_proj(
    const std::shared_ptr<ComprehensivePatterns::State> &s) {
  unsigned int v = s->state_value;
  unsigned int d = s->state_data;
  return (v + d);
}

__attribute__((pure)) unsigned int ComprehensivePatterns::nested_lets_same_base(
    const std::shared_ptr<ComprehensivePatterns::State> &s) {
  unsigned int v = s->state_value;
  unsigned int d = s->state_data;
  return (v + d);
}

__attribute__((pure)) unsigned int ComprehensivePatterns::if_with_proj(
    const std::shared_ptr<ComprehensivePatterns::State> &s) {
  if (s->state_value == 0u) {
    return s->state_data;
  } else {
    return s->state_value;
  }
}

__attribute__((pure)) unsigned int ComprehensivePatterns::match_scrutinee_proj(
    const std::shared_ptr<ComprehensivePatterns::State> &s) {
  if (s->state_value <= 0) {
    return s->state_data;
  } else {
    unsigned int n = s->state_value - 1;
    return n;
  }
}

__attribute__((pure))
std::pair<std::shared_ptr<ComprehensivePatterns::State>, unsigned int>
ComprehensivePatterns::bind_proj_use_base(
    std::shared_ptr<ComprehensivePatterns::State> s) {
  unsigned int v = s->state_value;
  return std::make_pair(std::move(s), v);
}

std::shared_ptr<ComprehensivePatterns::RSeq> ComprehensivePatterns::side_effect(
    std::shared_ptr<ComprehensivePatterns::RSeq> r) {
  return r;
}

__attribute__((pure)) unsigned int ComprehensivePatterns::after_side_effect(
    const std::shared_ptr<ComprehensivePatterns::RSeq> &r) {
  std::shared_ptr<ComprehensivePatterns::RSeq> r2 = side_effect(r);
  return std::move(r2)->seq_val;
}

__attribute__((pure)) unsigned int ComprehensivePatterns::two_side_effects(
    const std::shared_ptr<ComprehensivePatterns::RSeq> &r) {
  std::shared_ptr<ComprehensivePatterns::RSeq> r2 = side_effect(r);
  std::shared_ptr<ComprehensivePatterns::RSeq> r3 = side_effect(std::move(r2));
  return std::move(r3)->seq_val;
}

__attribute__((pure)) unsigned int ComprehensivePatterns::side_effect_in_branch(
    const bool b, const std::shared_ptr<ComprehensivePatterns::RSeq> &r) {
  std::shared_ptr<ComprehensivePatterns::RSeq> r2;
  if (b) {
    r2 = side_effect(r);
  } else {
    r2 = r;
  }
  return std::move(r2)->seq_val;
}

__attribute__((pure)) unsigned int ComprehensivePatterns::return_proj_stmt(
    const std::shared_ptr<ComprehensivePatterns::StateStmt> &s) {
  return s->stmt_value;
}

__attribute__((pure)) unsigned int ComprehensivePatterns::return_complex(
    const std::shared_ptr<ComprehensivePatterns::StateStmt> &s) {
  return (s->stmt_value + s->stmt_data);
}

__attribute__((pure)) std::pair<unsigned int, unsigned int>
ComprehensivePatterns::return_pair(
    const std::shared_ptr<ComprehensivePatterns::StateStmt> &s) {
  return std::make_pair(s->stmt_value, s->stmt_data);
}

__attribute__((pure)) unsigned int ComprehensivePatterns::chained_proj(
    const std::shared_ptr<ComprehensivePatterns::OuterStmt> &o) {
  return o->outer_stmt_inner->inner_stmt_val;
}

__attribute__((pure)) unsigned int ComprehensivePatterns::triple_chain(
    const std::shared_ptr<ComprehensivePatterns::Level3Stmt> &l3) {
  return l3->l3_outer_stmt->outer_stmt_inner->inner_stmt_val;
}

__attribute__((pure)) unsigned int ComprehensivePatterns::proj_in_arith(
    const std::shared_ptr<ComprehensivePatterns::StateStmt> &s) {
  return (s->stmt_value + 10u);
}

__attribute__((pure)) unsigned int ComprehensivePatterns::multi_proj_expr(
    const std::shared_ptr<ComprehensivePatterns::StateStmt> &s) {
  return (s->stmt_value + (s->stmt_data * 2u));
}

std::shared_ptr<List<unsigned int>> ComprehensivePatterns::proj_in_list(
    const std::shared_ptr<ComprehensivePatterns::StateStmt> &s) {
  return List<unsigned int>::cons(
      s->stmt_value,
      List<unsigned int>::cons(s->stmt_data, List<unsigned int>::nil()));
}

__attribute__((pure)) bool ComprehensivePatterns::compare_projs(
    const std::shared_ptr<ComprehensivePatterns::StateStmt> &s) {
  return s->stmt_value == s->stmt_data;
}

__attribute__((pure)) bool ComprehensivePatterns::bool_with_proj(
    const std::shared_ptr<ComprehensivePatterns::StateStmt> &s) {
  return !(s->stmt_value == 0u);
}

__attribute__((pure)) unsigned int ComprehensivePatterns::sum_values(
    const unsigned int n,
    const std::shared_ptr<ComprehensivePatterns::StateStmt> &s) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    decltype(std::declval<
                 const std::shared_ptr<ComprehensivePatterns::StateStmt> &>()
                 ->stmt_value) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            const unsigned int n = _f.n;
                            if (n <= 0) {
                              _result = 0u;
                            } else {
                              unsigned int m = n - 1;
                              _stack.emplace_back(_Call1{s->stmt_value});
                              _stack.emplace_back(_Enter{m});
                            }
                          },
                          [&](_Call1 _f) { _result = (_f._s0 + _result); }},
               _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int ComprehensivePatterns::branch_use(
    const bool b, const std::shared_ptr<ComprehensivePatterns::RCF> &r) {
  if (b) {
    return r->cf_val;
  } else {
    return r->cf_val;
  }
}

__attribute__((pure))
std::pair<std::shared_ptr<ComprehensivePatterns::RCF>, unsigned int>
ComprehensivePatterns::branch_different(
    const bool b, std::shared_ptr<ComprehensivePatterns::RCF> r) {
  if (b) {
    return std::make_pair(r, r->cf_val);
  } else {
    return std::make_pair(std::move(r), 0u);
  }
}

__attribute__((pure)) unsigned int ComprehensivePatterns::match_with_wild(
    const std::optional<std::shared_ptr<ComprehensivePatterns::RCF>> o) {
  if (o.has_value()) {
    const std::shared_ptr<ComprehensivePatterns::RCF> &r = *o;
    return r->cf_val;
  } else {
    return 0u;
  }
}

__attribute__((pure)) unsigned int ComprehensivePatterns::sum_with_state(
    const unsigned int n,
    const std::shared_ptr<ComprehensivePatterns::RCF> &r) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    decltype(std::declval<const std::shared_ptr<ComprehensivePatterns::RCF> &>()
                 ->cf_val) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            const unsigned int n = _f.n;
                            if (n <= 0) {
                              _result = r->cf_val;
                            } else {
                              unsigned int m = n - 1;
                              _stack.emplace_back(_Call1{r->cf_val});
                              _stack.emplace_back(_Enter{m});
                            }
                          },
                          [&](_Call1 _f) { _result = (_f._s0 + _result); }},
               _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int ComprehensivePatterns::even_count(
    const unsigned int n,
    const std::shared_ptr<ComprehensivePatterns::RCF> &r) {
  if (n <= 0) {
    return 0u;
  } else {
    unsigned int m = n - 1;
    return (1u + odd_count(m, r));
  }
}

__attribute__((pure)) unsigned int ComprehensivePatterns::odd_count(
    const unsigned int n,
    const std::shared_ptr<ComprehensivePatterns::RCF> &r) {
  if (n <= 0) {
    return r->cf_val;
  } else {
    unsigned int m = n - 1;
    return (1u + even_count(m, r));
  }
}

__attribute__((pure)) unsigned int ComprehensivePatterns::accum_with_state(
    const unsigned int n,
    const std::shared_ptr<ComprehensivePatterns::StateLB> &s) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    decltype(std::declval<
                 const std::shared_ptr<ComprehensivePatterns::StateLB> &>()
                 ->lb_value) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            const unsigned int n = _f.n;
                            if (n <= 0) {
                              _result = s->lb_value;
                            } else {
                              unsigned int m = n - 1;
                              _stack.emplace_back(_Call1{s->lb_value});
                              _stack.emplace_back(_Enter{m});
                            }
                          },
                          [&](_Call1 _f) { _result = (_f._s0 + _result); }},
               _frame);
  }
  return _result;
}

std::shared_ptr<ComprehensivePatterns::StateOP> ComprehensivePatterns::identity(
    std::shared_ptr<ComprehensivePatterns::StateOP> s) {
  return s;
}

__attribute__((pure)) unsigned int ComprehensivePatterns::extract_via_match(
    const std::shared_ptr<ComprehensivePatterns::StateOP> &s) {
  return identity(s)->op_value;
}

std::shared_ptr<ComprehensivePatterns::StateOP>
ComprehensivePatterns::consume_state(
    std::shared_ptr<ComprehensivePatterns::StateOP> s) {
  return s;
}

__attribute__((pure)) unsigned int ComprehensivePatterns::match_consumed(
    const std::shared_ptr<ComprehensivePatterns::StateOP> &s) {
  return consume_state(s)->op_value;
}

__attribute__((pure))
std::pair<std::shared_ptr<ComprehensivePatterns::StateOP>, unsigned int>
ComprehensivePatterns::force_owned(
    std::shared_ptr<ComprehensivePatterns::StateOP> s) {
  unsigned int result = s->op_value;
  return std::make_pair(std::move(s), result);
}

__attribute__((pure))
std::pair<std::pair<std::shared_ptr<ComprehensivePatterns::StateOP>,
                    std::shared_ptr<ComprehensivePatterns::StateOP>>,
          unsigned int>
ComprehensivePatterns::pair_then_match(
    std::shared_ptr<ComprehensivePatterns::StateOP> s) {
  std::pair<std::shared_ptr<ComprehensivePatterns::StateOP>,
            std::shared_ptr<ComprehensivePatterns::StateOP>>
      p = std::make_pair(s, s);
  unsigned int x = std::move(s)->op_value;
  return std::make_pair(p, x);
}
