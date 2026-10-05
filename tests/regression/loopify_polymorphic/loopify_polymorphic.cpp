#include "loopify_polymorphic.h"

uint64_t LoopifyPolymorphic::nat_length(const List<uint64_t> &x0_) {
  return poly_length<uint64_t>(x0_);
}

List<uint64_t> LoopifyPolymorphic::nat_reverse(const List<uint64_t> &x0_) {
  return poly_reverse<uint64_t>(x0_);
}

List<uint64_t> LoopifyPolymorphic::nat_append(const List<uint64_t> &x0_,
                                              const List<uint64_t> &x1_) {
  return poly_append<uint64_t>(x0_, x1_);
}

std::optional<uint64_t>
LoopifyPolymorphic::nat_last(const List<uint64_t> &x0_) {
  return poly_last<uint64_t>(x0_);
}

List<uint64_t> LoopifyPolymorphic::nat_take(uint64_t x0_,
                                            const List<uint64_t> &x1_) {
  return poly_take<uint64_t>(x0_, x1_);
}

List<uint64_t> LoopifyPolymorphic::nat_drop(uint64_t x0_,
                                            const List<uint64_t> &x1_) {
  return poly_drop<uint64_t>(x0_, x1_);
}

std::optional<uint64_t> LoopifyPolymorphic::nat_nth(uint64_t x0_,
                                                    const List<uint64_t> &x1_) {
  return poly_nth<uint64_t>(x0_, x1_);
}

bool LoopifyPolymorphic::nat_eq(uint64_t x0_, uint64_t x1_) {
  return x0_ == x1_;
}

bool LoopifyPolymorphic::is_even(uint64_t x) {
  return (UINT64_C(2) ? x % UINT64_C(2) : x) == UINT64_C(0);
}

bool LoopifyPolymorphic::nat_member(uint64_t x0_, const List<uint64_t> &x1_) {
  return poly_member<uint64_t>(nat_eq, x0_, x1_);
}

List<uint64_t> LoopifyPolymorphic::nat_replicate(uint64_t x0_, uint64_t x1_) {
  return poly_replicate<uint64_t>(x0_, x1_);
}
