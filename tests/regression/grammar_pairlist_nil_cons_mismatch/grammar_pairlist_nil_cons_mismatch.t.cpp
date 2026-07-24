#include <grammar_pairlist_nil_cons_mismatch.h>

#include <any>
#include <cassert>
#include <functional>
#include <iostream>

// Regression driver for a value-dependent PAIR-ELEMENT list
// (list (string*nat)) erasure fix, a narrower recurrence of the
// obj_nil_erasure_mismatch bug.
//
// Two erasure-shape bugs were fixed here:
//
//  1. For the [Pairs] and [Obj] nonterminals (both typed [list
//     (string*nat)]), the "nil" production used to erase to
//     [std::deque<std::pair<std::any,std::any>>{}] while the "cons"
//     production erased to [std::deque<std::any>{ any(pr), ... }] -- two
//     DIFFERENT runtime container shapes for the same Coq type. A consumer
//     (Obj's [pr :: prs] recursion, and ultimately Doc's [mkVal]) that
//     any_cast<>s using one shape crashed with std::bad_any_cast on the
//     other.  Every producer of an erased [list (string*nat)] action now
//     erases to the SAME canonical representation ([std::deque<std::any>]).
//
//  2. [Pair]'s own action builds its [(string*nat)] result one component at
//     a time from an erased tuple scrutinee whose own component types are
//     not statically resolvable at that construction site (the enclosing
//     grammar machinery is generic over the nonterminal), so it stores
//     [std::pair<std::any,std::any>] (each component still boxed as
//     [std::any]) rather than the fully concrete [std::pair<String,
//     uint64_t>] a naive [std::any_cast] would expect. [crane_any_cast] (see
//     crane_fn.h) recovers a concrete pair from this per-component-boxed
//     representation, so [crane_container_cast]-based consumers like Doc's
//     [mkVal] now unbox each element correctly.
//
// Building a non-empty object (mirroring JSON's `{"a":1,"b":2}`) succeeds
// end-to-end through Pair's action, Obj's cons, and Doc's [mkVal] wrapper.

namespace {

// entries[i].a1 is `production_semty = pair<predicate_semty, action_semty>`;
// `.second` is the boxed `action_semty = std::any` holding the
// `std::function<std::any(std::any)>` action closure (see crane_fn.h's
// [crane_erase_fn]).
std::any call_action(const grammar_entry &e, std::any arg) {
  auto act = std::any_cast<std::function<std::any(std::any)>>(e.a1.second);
  return act(std::move(arg));
}

// Crane's extracted [string] is its own cons-list-of-[Ascii] representation
// ([String]), not [std::string] -- a terminal's STR token, as produced by
// the real lexer/action machinery, would carry a [String] value.  Build one
// from a [std::string] bit-by-bit (LSB-first, matching Coq's [ascii_of_nat]
// convention) so this test exercises the same runtime shape a real STR
// action would.
String make_string(const std::string &s) {
  String acc = String::emptystring();
  for (auto it = s.rbegin(); it != s.rend(); ++it) {
    unsigned char c = static_cast<unsigned char>(*it);
    Ascii a = Ascii::ascii0((c >> 0) & 1, (c >> 1) & 1, (c >> 2) & 1,
                             (c >> 3) & 1, (c >> 4) & 1, (c >> 5) & 1,
                             (c >> 6) & 1, (c >> 7) & 1);
    acc = String::string0(a, std::move(acc));
  }
  return acc;
}

} // namespace

int main() {
  // entries: [Doc; Obj-cons; Obj-nil; Pairs-cons; Pairs-nil; Pair]
  assert(entries.size() == 6);
  const grammar_entry &doc_entry = entries[0];
  const grammar_entry &obj_cons_entry = entries[1];
  const grammar_entry &pairs_cons_entry = entries[3];
  const grammar_entry &pairs_nil_entry = entries[4];
  const grammar_entry &pair_entry = entries[5];

  assert(doc_entry.x.first == Nonterminal::DOC);
  assert(obj_cons_entry.x.first == Nonterminal::OBJ);
  assert(pairs_cons_entry.x.first == Nonterminal::PAIRS);
  assert(pairs_nil_entry.x.first == Nonterminal::PAIRS);
  assert(pair_entry.x.first == Nonterminal::PAIR);

  // Build Pair("b", 2): Pair's action destructures (s, (_, (n, ()))).
  auto make_pair_tup = [](std::any s, std::any n) {
    return std::any(std::make_pair(
        std::move(s),
        std::any(std::make_pair(std::any{},
                                 std::any(std::make_pair(std::move(n),
                                                          std::any{}))))));
  };
  std::any pair_b = call_action(
      pair_entry, make_pair_tup(std::any(make_string("b")), std::any(uint64_t(2))));

  // Pairs-nil: [] -> std::deque<std::any>{}
  std::any pairs_nil = call_action(pairs_nil_entry, std::any{});
  auto nil_list = std::any_cast<std::deque<std::any>>(pairs_nil);
  assert(nil_list.empty());

  // Pairs-cons: (_, (pr, (prs, _))) -> pr :: prs, built on top of nil,
  // giving Pairs = [("b", 2)].
  auto make_pairs_cons_tup = [](std::any pr, std::any prs) {
    return std::any(std::make_pair(
        std::any{},
        std::any(std::make_pair(std::move(pr),
                                 std::any(std::make_pair(std::move(prs),
                                                          std::any{}))))));
  };
  std::any pairs_one =
      call_action(pairs_cons_entry, make_pairs_cons_tup(pair_b, pairs_nil));
  auto pairs_one_list = std::any_cast<std::deque<std::any>>(pairs_one);
  assert(pairs_one_list.size() == 1);

  // Build Pair("a", 1) the same way, then Obj-cons: pr :: prs, giving
  // Obj = [("a", 1); ("b", 2)] -- a NON-EMPTY nested-pair list, the case
  // that used to throw std::bad_any_cast.
  std::any pair_a = call_action(
      pair_entry, make_pair_tup(std::any(make_string("a")), std::any(uint64_t(1))));
  auto make_obj_cons_tup = [](std::any pr, std::any prs) {
    return std::any(std::make_pair(
        std::any{},
        std::any(std::make_pair(
            std::move(pr),
            std::any(std::make_pair(
                std::move(prs), std::any(std::make_pair(std::any{}, std::any{})))))))
        );
  };
  std::any obj_list_any =
      call_action(obj_cons_entry, make_obj_cons_tup(pair_a, pairs_one));
  auto obj_list = std::any_cast<std::deque<std::any>>(obj_list_any);
  assert(obj_list.size() == 2);

  // Finally, Doc's action wraps Obj's result into [val]. This is the
  // consumer boundary that used to be exercised by the reported
  // std::bad_any_cast on non-empty objects.
  auto doc_tup = std::any(std::make_pair(obj_list_any, std::any{}));
  std::any val_any = call_action(doc_entry, doc_tup);
  val v = std::any_cast<val>(val_any);

  assert(v.pairs.size() == 2);
  assert(v.pairs[0].second == 1);
  assert(v.pairs[1].second == 2);

  std::cout << "grammar_pairlist_nil_cons_mismatch: nil/cons erase "
               "consistently, end-to-end mkVal succeeded."
            << std::endl;
  return 0;
}
