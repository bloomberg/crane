#include <promoted_var_collapse.h>

#include <cassert>
#include <string>

struct MyProv {
  using provenance = int;
  using allocationId = std::string;
  using prov = double;
  static Nat prov_size(const prov &) { return Nat::o(); }
};

struct MyParams {
  using PROV = MyProv;
  static Nat width() { return Nat::s(Nat::o()); }
};

int main() {
  // Each associated type must keep its own identity: the call only compiles
  // when the three parameters are spelled allocationId, prov and list prov.
  Nat r = PromotedVarCollapse::takes_three<MyParams>(
      std::string("a"), 1.5, List<double>::nil(), Nat::o());
  assert(std::holds_alternative<Nat::S>(r.v()));
  return 0;
}
