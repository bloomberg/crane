#include <name_clash_match_match.h>

#include <cassert>

int main() {
  using NS = NameClashMatchMatch;

  auto leaf = NS::tree::leaf();
  auto t = NS::tree::node(NS::tree::node(NS::tree::leaf(), 10u, NS::tree::leaf()),
                           20u,
                           NS::tree::node(NS::tree::leaf(), 30u, NS::tree::leaf()));

  assert(NS::subtree_value(NS::Dir::e_GOLEFT, t) == 10u);
  assert(NS::subtree_value(NS::Dir::e_GORIGHT, t) == 30u);
  assert(NS::subtree_value(NS::Dir::e_GOLEFT, leaf) == 0u);

  assert(NS::inline_match_match(NS::Dir::e_GOLEFT, t) == 20u);
  assert(NS::inline_match_match(NS::Dir::e_GORIGHT, t) == 100u);

  assert(NS::double_match(t) == 30u);
  assert(NS::double_match(leaf) == 1u);

  assert(NS::chained(leaf) == 42u);
  assert(NS::chained(t) == 20u);

  return 0;
}
