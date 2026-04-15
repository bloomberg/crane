#include <name_clash_let_match.h>

#include <cassert>

int main() {
  using NS = NameClashLetMatch;

  // let_shadows_match: method on either
  assert(NS::either::left(42)->let_shadows_match() == 42u);
  assert(NS::either::right(5)->let_shadows_match() == 105u);

  // match_then_let: method on either
  assert(NS::either::left(10)->match_then_let() == 11u);
  assert(NS::either::right(7)->match_then_let() == 7u);

  // two_eithers: method on either (e1), takes e2
  assert(NS::either::left(10)->two_eithers(NS::either::left(20)) == 30u);
  assert(NS::either::right(10)->two_eithers(NS::either::right(20)) == 80u);

  // triple_then_either: method on triple, takes either
  assert(NS::triple::mktriple(1, 2, 3)->triple_then_either(NS::either::left(4)) == 10u);

  // deep_let_match: method on either (e1), takes e2 and e3
  assert(NS::either::left(10)->deep_let_match(NS::either::left(20),
                                                NS::either::left(30)) == 60u);

  // same_name_branches: static function
  assert(NS::same_name_branches(NS::either::left(1),
                                 NS::triple::mktriple(2, 3, 4)) == 10u);
  assert(NS::same_name_branches(NS::either::right(2),
                                 NS::triple::mktriple(3, 4, 5)) == 120u);

  return 0;
}
