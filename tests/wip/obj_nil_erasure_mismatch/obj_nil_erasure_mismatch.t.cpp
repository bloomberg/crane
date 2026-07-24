#include <obj_nil_erasure_mismatch.h>

#include <any>
#include <cassert>
#include <deque>
#include <iostream>

// This mirrors the real crash observed when running the extracted C++
// JSON/PPM/Newick parsers on real input containing an object/list: a
// consumer that any_casts a list-of-pairs value using the shape the
// "cons" production erases to gets a std::bad_any_cast when the value
// actually came from the "nil" production of the *same* nonterminal.
int main() {
  assert(entries.size() == 5);

  // entries[3] is the TOPSYM "cons" production: [(7,8)].
  // entries[4] is the TOPSYM "nil" production: [].
  const auto &cons_entry = entries[3];
  const auto &nil_entry = entries[4];
  assert(cons_entry.x == Sym::TOPSYM);
  assert(nil_entry.x == Sym::TOPSYM);

  std::any cons_v = cons_entry.a1(Unit::TT);
  std::any nil_v = nil_entry.a1(Unit::TT);

  // The "cons" production's erased value is a std::deque<Prod<Nat,Nat>>.
  auto cons_list = std::any_cast<std::deque<Prod<Nat, Nat>>>(cons_v);
  std::cout << "cons case: any_cast<deque<Prod<Nat,Nat>>> succeeded, size="
            << cons_list.size() << std::endl;

  // The "nil" production of the *same* nonterminal (TOPSYM) erases its
  // value as std::deque<Prod<std::any,std::any>> instead -- a different
  // C++ type for the same Coq type `list (nat * nat)`. A consumer that
  // (correctly, per the cons case) expects std::deque<Prod<Nat,Nat>> gets
  // std::bad_any_cast here, exactly like the real extracted JSON parser
  // crashing on any JSON object.
  bool threw = false;
  try {
    auto nil_list = std::any_cast<std::deque<Prod<Nat, Nat>>>(nil_v);
    (void)nil_list;
  } catch (const std::bad_any_cast &) {
    threw = true;
  }

  std::cout << "nil case any_cast<deque<Prod<Nat,Nat>>> threw bad_any_cast: "
            << threw << std::endl;
  assert(threw);

  std::cout << "obj_nil_erasure_mismatch: reproduced the erasure mismatch."
            << std::endl;
  return 0;
}
