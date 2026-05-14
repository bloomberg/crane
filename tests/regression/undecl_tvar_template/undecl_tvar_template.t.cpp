// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// Regression: a polymorphic function {A : Type} inside a functor module
// must generate template <typename T1> even when the enclosing struct is
// already a template struct (no undeclared identifier T1).

#include "UndeclTvarTemplate.h"
#include "Datatypes.h"

struct CharTy {
  using Sigma = char;
};

int main() {
  const Datatypes::List<int> l = Datatypes::List<int>::cons(1, Datatypes::List<int>::nil());
  const Datatypes::List<char> s = Datatypes::List<char>::nil();
  const auto v = UndeclTvarTemplate::Make<CharTy>::String_dec<int>(l, s);
  (void)v;
  return 0;
}
