#include <loopify_polymorphic.h>

unsigned int LoopifyPolymorphic::nat_length(const List<unsigned int> &_x0) {
  return poly_length<unsigned int>(_x0);
}

List<unsigned int>
LoopifyPolymorphic::nat_reverse(const List<unsigned int> &_x0) {
  return poly_reverse<unsigned int>(_x0);
}

List<unsigned int>
LoopifyPolymorphic::nat_append(const List<unsigned int> &_x0,
                               const List<unsigned int> &_x1) {
  return poly_append<unsigned int>(_x0, _x1);
}

std::optional<unsigned int>
LoopifyPolymorphic::nat_last(const List<unsigned int> &_x0) {
  return poly_last<unsigned int>(_x0);
}

List<unsigned int> LoopifyPolymorphic::nat_take(const unsigned int &_x0,
                                                const List<unsigned int> &_x1) {
  return poly_take<unsigned int>(_x0, _x1);
}

List<unsigned int> LoopifyPolymorphic::nat_drop(const unsigned int &_x0,
                                                const List<unsigned int> &_x1) {
  return poly_drop<unsigned int>(_x0, _x1);
}

std::optional<unsigned int>
LoopifyPolymorphic::nat_nth(const unsigned int &_x0,
                            const List<unsigned int> &_x1) {
  return poly_nth<unsigned int>(_x0, _x1);
}

bool LoopifyPolymorphic::nat_eq(const unsigned int &_x0,
                                const unsigned int &_x1) {
  return _x0 == _x1;
}

bool LoopifyPolymorphic::is_even(const unsigned int &x) {
  return (2u ? x % 2u : x) == 0u;
}

bool LoopifyPolymorphic::nat_member(const unsigned int &_x0,
                                    const List<unsigned int> &_x1) {
  return poly_member<unsigned int>(nat_eq, _x0, _x1);
}

List<unsigned int> LoopifyPolymorphic::nat_replicate(const unsigned int &_x0,
                                                     const unsigned int &_x1) {
  return poly_replicate<unsigned int>(_x0, _x1);
}
