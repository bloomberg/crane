#include <lambda_binder_from_callee.h>

#include <cassert>
#include <string>

struct MyProv {
  using provenance = int;
  using allocationId = std::string;
  using prov = double;
  static std::string mk_aid(const Nat &) { return std::string("ab"); }
  static Nat aid_size(const std::string &s) {
    return s.size() == 2 ? Nat::s(Nat::s(Nat::o())) : Nat::o();
  }
};

struct MyParams {
  using PROV = MyProv;
  static Nat width() { return Nat::o(); }
};

int main() {
  // The lambda's binder must be spelled allocationId, not whichever
  // associated type the carrier guess happens to hold.
  Nat r = LambdaBinderFromCallee::use<MyParams>();
  assert(std::holds_alternative<Nat::S>(r.v()));
  return 0;
}
