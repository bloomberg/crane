#include "st_refs.h"

std::pair<uint64_t, uint64_t> new_and_read_both_nat(STRefs) {
  uint64_t r1 = UINT64_C(5);
  uint64_t r2 = UINT64_C(6);
  return std::make_pair(r1, r2);
}

uint64_t tree_simp_nat(STRefs) {
  uint64_t v = UINT64_C(5);
  return v;
}

uint64_t tree_simp_another_nat(STRefs) {
  uint64_t v = UINT64_C(5);
  v = UINT64_C(6);
  return v;
}

void swap(STRefs, uint64_t *v, uint64_t *w) {
  uint64_t a = *v;
  uint64_t b = *w;
  *v = b;
  *w = a;
}

std::pair<uint64_t, uint64_t> swapped(STRefs r) {
  uint64_t v = UINT64_C(1);
  uint64_t w = UINT64_C(2);
  swap(r, &v, &w);
  return std::make_pair(v, w);
}

std::pair<bool, bool> new_and_read_both_bool(STRefs) {
  bool r1 = false;
  bool r2 = true;
  return std::make_pair(r1, r2);
}

bool tree_simp_bool(STRefs) {
  bool v = true;
  return v;
}
