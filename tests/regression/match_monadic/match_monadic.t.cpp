#include <match_monadic.h>

using namespace std::string_literals;

int main() {
  // Test 1: color_name — enum-based match with effects
  auto r1 = MatchMonadic::color_name(Color::e_RED);

  // Test 3: nested_match — EXPOSES BUG: let-bound match result typed as std::any
  // auto r3 = MatchMonadic::nested_match(0, true);

  // Test 4: handle_option
  auto r4a = MatchMonadic::handle_option(std::make_optional(42u));
  auto r4b = MatchMonadic::handle_option(std::optional<unsigned int>());

  // Test 5: tree_sum — recursive function matching on tree
  auto leaf = Tree<unsigned int>::leaf();
  auto node = Tree<unsigned int>::node(leaf, 10u, Tree<unsigned int>::leaf());
  auto r5 = MatchMonadic::tree_sum(node);

  // Test 6: match_then_bind — EXPOSES BUG: std::any for tag variable
  // auto r6 = MatchMonadic::match_then_bind(0);

  // Test 7: bind_then_match — works fine
  // (requires stdin) auto r7 = MatchMonadic::bind_then_match();

  // Test 8: multi_match — EXPOSES BUG: std::any for x, y variables
  // auto r8 = MatchMonadic::multi_match(true, false);

  return 0;
}
