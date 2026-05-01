#include <name_clash_return_this.h>

#include <cassert>
#include <variant>

int main() {
  using NS = NameClashReturnThis;

  auto c5 = NS::shape::circle(5);
  auto s34 = NS::shape::square(3, 4);

  // maybe_transform true: transforms shape
  auto t1 = NS::maybe_transform(true, c5);
  assert(std::holds_alternative<NS::shape::Square>(t1.v()));

  // maybe_transform false: returns same shape
  auto t2 = NS::maybe_transform(false, c5);
  assert(std::holds_alternative<NS::shape::Circle>(t2.v()));

  // identity_or_double
  auto d = NS::identity_or_double(NS::shape::circle(3));
  assert(std::holds_alternative<NS::shape::Circle>(d.v()));
  assert(std::get<NS::shape::Circle>(d.v()).d_a0 == 6u);

  // pick_shape
  auto p = NS::pick_shape(c5, s34);
  assert(std::holds_alternative<NS::shape::Square>(p.v()));
  auto p2 = NS::pick_shape(s34, c5);
  assert(std::holds_alternative<NS::shape::Square>(p2.v()));

  // nested_this
  assert(NS::nested_this(NS::shape::circle(4)) == 8u);

  return 0;
}
