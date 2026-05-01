#include <closure_escape_match.h>

#include <cassert>
#include <iostream>

int main() {
  using L = ClosureEscapeMatch::mylist<unsigned int>;
  using LL = ClosureEscapeMatch::mylist<L>;

  // --- make_prepender_opt ---
  // Extract a closure from a match (inside an option), then use it
  // AFTER the original data has been destroyed.
  {
    auto inner = L::mycons(10u, L::mycons(20u, L::mynil()));
    auto outer = LL::mycons(inner, LL::mynil());

    auto opt = ClosureEscapeMatch::make_prepender_opt(outer);
    assert(opt.has_value());
    auto prepender = *opt;

    // Drop everything except the closure
    outer = LL::mynil();
    inner = L::mynil();
    opt.reset();

    auto arg = L::mycons(30u, L::mynil());
    auto result = prepender(arg);

    // Expect: app [10, 20] [30] = [10, 20, 30]
    auto &c1 = std::get<1>(result.v());
    assert(c1.d_a0 == 10u);
    auto &c2 = std::get<1>(c1.d_a1->v());
    assert(c2.d_a0 == 20u);
    auto &c3 = std::get<1>(c2.d_a1->v());
    assert(c3.d_a0 == 30u);
    std::cout << "make_prepender_opt: OK" << std::endl;
  }

  // --- make_pair_fn_opt ---
  {
    auto l = L::mycons(42u, L::mycons(1u, L::mycons(2u, L::mynil())));
    auto opt = ClosureEscapeMatch::make_pair_fn_opt(l);
    assert(opt.has_value());
    auto fn = *opt;
    l = L::mynil();
    opt.reset();
    auto [fst, snd] = fn({});
    assert(fst == 42u);
    assert(snd == 2u);
    std::cout << "make_pair_fn_opt: OK" << std::endl;
  }

  // --- nested_closure_opt ---
  {
    auto a = L::mycons(100u, L::mynil());
    auto b = L::mycons(200u, L::mynil());
    auto opt = ClosureEscapeMatch::nested_closure_opt(a, b);
    assert(opt.has_value());
    auto fn = *opt;
    a = L::mynil();
    b = L::mynil();
    opt.reset();
    unsigned int r = fn(5u);
    assert(r == 305u);
    std::cout << "nested_closure_opt: OK" << std::endl;
  }

  // --- closure_in_pair ---
  {
    auto inner = L::mycons(10u, L::mycons(20u, L::mynil()));
    auto outer = LL::mycons(inner, LL::mynil());
    auto [count, prepender] = ClosureEscapeMatch::closure_in_pair(outer);
    outer = LL::mynil();
    inner = L::mynil();
    assert(count == 2u);
    auto arg = L::mycons(30u, L::mynil());
    auto result = prepender(arg);
    auto &c1 = std::get<1>(result.v());
    assert(c1.d_a0 == 10u);
    std::cout << "closure_in_pair: OK" << std::endl;
  }

  return 0;
}
