#include <grammar_pairlist_nil_cons_mismatch.h>
#include <any>
#include <cstdio>
#include <cstdlib>
#include <functional>
#include <utility>

// Locates the (predicate, action) pair for a grammar entry matching a given
// nonterminal and right-hand-side arity (enough to disambiguate here).
static const std::pair<std::any, std::any> &
find_entry(Nonterminal nt, std::size_t arity) {
  for (const auto &e : entries) {
    if (e.x.first == nt && e.x.second.size() == arity) {
      return e.a1;
    }
  }
  std::fprintf(stderr, "no matching grammar entry found\n");
  std::exit(1);
}

int main() {
  // Pairs -> []  (nil): erases to std::deque<std::pair<std::any,std::any>>{}
  const auto &pairs_nil = find_entry(Nonterminal::PAIRS, 0);
  auto nil_action = std::any_cast<std::function<std::any(std::any)>>(pairs_nil.second);
  std::any nil_result = nil_action(std::any{});

  // Pair -> [STR; COLON; NAT], action: (s, n)
  const auto &pair_entry = find_entry(Nonterminal::PAIR, 3);
  auto pair_action = std::any_cast<std::function<std::any(std::any)>>(pair_entry.second);
  std::any pair_tup = std::any(std::make_pair(
      std::any(std::string("a")),
      std::any(std::make_pair(std::any{},
                               std::any(std::make_pair(std::any(uint64_t(1)),
                                                        std::any{}))))));
  std::any pair_result = pair_action(pair_tup);

  // Pairs -> [COMMA; NT Pair; NT Pairs], action: pr :: prs. Feeds the NIL
  // production's result (a real, freshly-parsed "Pairs" value, exactly as the
  // runtime parser would forward it) into the CONS production as the "prs"
  // child, matching how parsing actually composes nonterminal results
  // bottom-up.
  const auto &pairs_cons = find_entry(Nonterminal::PAIRS, 3);
  auto cons_action = std::any_cast<std::function<std::any(std::any)>>(pairs_cons.second);
  std::any cons_tup = std::any(std::make_pair(
      std::any{},
      std::any(std::make_pair(
          pair_result, std::any(std::make_pair(nil_result, std::any{}))))));

  try {
    cons_action(cons_tup);
    std::fprintf(stderr, "expected std::bad_any_cast, but none was thrown\n");
    return 1;
  } catch (const std::bad_any_cast &e) {
    std::printf("reproduced: %s\n", e.what());
    return 0;
  }
}
