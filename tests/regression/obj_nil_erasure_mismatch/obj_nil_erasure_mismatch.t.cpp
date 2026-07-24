#include <obj_nil_erasure_mismatch.h>

#include <any>
#include <cassert>
#include <deque>
#include <iostream>

// Regression driver for the erasure-mismatch fix.  The bug was that, inside
// the heterogeneous `entries` list, the value-dependent action results of the
// SAME Coq type `list (nat*nat)` erased to DIFFERENT C++ types: a "cons"
// production erased to `std::deque<Prod<Nat,Nat>>` while the matching "nil"
// production erased to `std::deque<Prod<std::any,std::any>>`.  A consumer that
// any_cast<>s the value using one shape crashed with std::bad_any_cast on the
// other.
//
// After the fix, every producer of an erased `list (nat*nat)` action erases to
// the SAME canonical representation (`std::deque<std::any>`, each element a
// std::any holding a Prod<any,any>), so a single any_cast shape works for both
// the cons and nil productions of the same nonterminal.
int main() {
  assert(entries.size() == 5);

  // entries[3] is the TOPSYM "cons" production: [(7,8)].
  // entries[4] is the TOPSYM "nil" production:  [].
  const auto &cons_entry = entries[3];
  const auto &nil_entry = entries[4];
  assert(cons_entry.x == Sym::TOPSYM);
  assert(nil_entry.x == Sym::TOPSYM);

  std::any cons_v = cons_entry.a1(Unit::TT);
  std::any nil_v = nil_entry.a1(Unit::TT);

  // Both productions of the same nonterminal now erase to the SAME C++ type,
  // so the same any_cast shape succeeds for both -- no bad_any_cast.
  auto cons_list = std::any_cast<std::deque<std::any>>(cons_v);
  auto nil_list = std::any_cast<std::deque<std::any>>(nil_v);

  std::cout << "cons case: any_cast<deque<any>> succeeded, size="
            << cons_list.size() << std::endl;
  std::cout << "nil case:  any_cast<deque<any>> succeeded, size="
            << nil_list.size() << std::endl;

  assert(cons_list.size() == 1);
  assert(nil_list.size() == 0);

  // The single cons element unboxes to a Prod<any,any> pair; its components
  // unbox to Nat.  This confirms the concrete value survives the canonical
  // erasure.
  auto pair0 = std::any_cast<Prod<std::any, std::any>>(cons_list[0]);
  const Nat &fst = std::any_cast<const Nat &>(pair0.a0);
  const Nat &snd = std::any_cast<const Nat &>(pair0.a1);
  auto nat_to_int = [](const Nat &n) {
    int acc = 0;
    const Nat *cur = &n;
    while (std::holds_alternative<Nat::S>(cur->v())) {
      ++acc;
      cur = std::get<Nat::S>(cur->v()).a0.get();
    }
    return acc;
  };
  assert(nat_to_int(fst) == 7);
  assert(nat_to_int(snd) == 8);

  std::cout << "obj_nil_erasure_mismatch: cons and nil erase consistently."
            << std::endl;
  return 0;
}
