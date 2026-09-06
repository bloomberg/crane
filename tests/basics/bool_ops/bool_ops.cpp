#include "bool_ops.h"

bool BoolOps::my_negb(bool b) {
  if (b) {
    return false;
  } else {
    return true;
  }
}

bool BoolOps::my_andb(bool a, bool b) {
  if (a) {
    return b;
  } else {
    return false;
  }
}

bool BoolOps::my_orb(bool a, bool b) {
  if (a) {
    return true;
  } else {
    return b;
  }
}

bool BoolOps::my_xorb(bool a, bool b) {
  if (a) {
    if (b) {
      return false;
    } else {
      return true;
    }
  } else {
    if (b) {
      return true;
    } else {
      return false;
    }
  }
}

uint64_t BoolOps::if_nat(bool b, uint64_t t, uint64_t f) {
  if (b) {
    return t;
  } else {
    return f;
  }
}

bool BoolOps::complex_bool(bool a, bool b, bool c) {
  return my_orb(my_andb(a, b), my_andb(my_negb(a), c));
}

bool BoolOps::nat_eq(uint64_t x0_, uint64_t x1_) { return x0_ == x1_; }

bool BoolOps::nat_lt(uint64_t x0_, uint64_t x1_) { return x0_ < x1_; }

bool BoolOps::nat_le(uint64_t x0_, uint64_t x1_) { return x0_ <= x1_; }
