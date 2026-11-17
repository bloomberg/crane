#include "concept_prereq_in_collision.h"

bool AstLike::eq(const Nat &x0_, const Nat &x1_) { return x0_.eqb(x1_); }

Ident to_ident(const Nat &n) { return Ident::global(n); }

AstLike::key key_twice(Nat k) { return k.add(k); }
