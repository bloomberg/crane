// A promoted type variable no scope binds -- [prov], an associated type of
// Provenance that Params' concept mentions -- falls back to the file-scope
// alias its class leaves behind (ProvDef.h: using prov = crane::obj).  Under
// separate extraction that alias lives in ProvDef's namespace, so the using
// file declares `using ProvDef::prov;` and the bare `prov` in
// `requires ParamsDef::Params<_tcI0, prov>` resolves as it does in a
// single-file extraction.
#include "Datatypes.h"
#include "ProvDef.h"
#include "ParamsDef.h"
#include "SepExtPromotedAliasImport.h"

#include <cassert>

struct AnyParams {
  using PROV = int;
  using PTR = int;
};

static int to_int(const Datatypes::Nat &n) {
  int k = 0;
  for (const Datatypes::Nat *p = &n;
       std::holds_alternative<Datatypes::Nat::S>(p->v());
       p = std::get<Datatypes::Nat::S>(p->v()).a0.get())
    ++k;
  return k;
}

int main() {
  using M = SepExtPromotedAliasImport::Mbit<int>;
  auto two = Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::o()));
  assert(to_int(M::bit_byte(two).show<AnyParams>()) == 2);
  assert(to_int(M::bit_ptr(7).show<AnyParams>()) == 0);
  return 0;
}
