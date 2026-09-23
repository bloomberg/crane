#include <value_position_class_promoted.h>

#include <cassert>

struct MyPtr {
  using iptr = Nat;
  static VLike<Nat> VLike_iptr() {
    return VLike<Nat>{Nat::o(),
                      [](const Nat &a, const Nat &b) { return a.add(b); }};
  }
  static Nat one_iptr() { return Nat::s(Nat::o()); }
};

int main() {
  // VLike is used in value position, so it is a struct, not a concept: the
  // Ptr concept must ask for VLike_iptr as a function only.
  Nat r = ValuePositionClassPromoted::twice<MyPtr>();
  const auto &s = std::get<Nat::S>(r.v());
  assert(std::holds_alternative<Nat::S>(s.a0->v()));
  assert(std::holds_alternative<Nat::O>(
      ValuePositionClassPromoted::ndicts.v()));
  return 0;
}
