#include <name_clash_binding_reuse.h>

#include <cassert>

int main() {
  using NS = NameClashBindingReuse;

  auto p12 = NS::pair_nat::mkpairnat(1, 2);
  auto p34 = NS::pair_nat::mkpairnat(3, 4);
  auto t123 = NS::triple_nat::mktriplenat(1, 2, 3);

  // add_pairs: nested match, both on pair_nat
  assert(p12->add_pairs(p34) == 10u);

  // add_pairs_let: IIFE-wrapped matches
  assert(p12->add_pairs_let(p34) == 10u);

  // combine: triple + pair
  assert(t123->combine(p34) == 13u);

  // cascade
  auto c = t123->cascade();
  assert(std::get<NS::pair_nat::MkPairNat>(c->v()).d_a0 == 3u);
  assert(std::get<NS::pair_nat::MkPairNat>(c->v()).d_a1 == 3u);

  // cascade_and_match
  assert(t123->cascade_and_match() == 6u);

  // flat_combine: single-constructor nested match
  auto fc = p12->flat_combine(p34);
  assert(std::get<NS::pair_nat::MkPairNat>(fc->v()).d_a0 == 4u);
  assert(std::get<NS::pair_nat::MkPairNat>(fc->v()).d_a1 == 6u);

  return 0;
}
