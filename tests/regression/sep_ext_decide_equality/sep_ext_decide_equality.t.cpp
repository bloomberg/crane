// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// WIP: Lemma proved by `decide equality` inside a functor generates
// undeclared type variable T1 in the extracted C++ function.

#include "SepExtDecideEquality.h"
#include "Datatypes.h"

struct CharSigma {
  using Sigma = char;
  static bool Sigma_dec(char a, char b) { return a == b; }
};

int main() {
  const auto s1 = Datatypes::List<char>::cons('a', Datatypes::List<char>::nil());
  const auto s2 = Datatypes::List<char>::cons('a', Datatypes::List<char>::nil());
  const bool eq = SepExtDecideEquality::DefsFn<CharSigma>::Strings::String_dec(s1, s2);
  (void)eq;
  return 0;
}
