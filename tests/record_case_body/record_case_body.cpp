#include "record_case_body.h"

uint64_t RecordCaseBody::case_in_body(const RecordCaseBody::Rec &r) {
  uint64_t a = r.f1;
  uint64_t b = r.f2;
  uint64_t c = r.f3;
  if (a <= 0) {
    return (b + c);
  } else {
    uint64_t n = a - 1;
    return ((n + b) + c);
  }
}

uint64_t RecordCaseBody::helper(uint64_t n) {
  if (n <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t n_ = n - 1;
    return (n + helper(n_));
  }
}

uint64_t RecordCaseBody::fix_in_body(const RecordCaseBody::Rec &r) {
  uint64_t a = r.f1;
  uint64_t b = r.f2;
  uint64_t c = r.f3;
  return helper(((a + b) + c));
}

uint64_t RecordCaseBody::let_in_body(const RecordCaseBody::Rec &r) {
  uint64_t a = r.f1;
  uint64_t b = r.f2;
  uint64_t c = r.f3;
  uint64_t x = (a + b);
  uint64_t y = (x + c);
  uint64_t z = (y * UINT64_C(2));
  if (z <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t _x = z - 1;
    return z;
  }
}

uint64_t RecordCaseBody::apply_nonfld(const RecordCaseBody::Rec &r) {
  uint64_t a = r.f1;
  uint64_t b = r.f2;
  uint64_t c = r.f3;
  return ((((a + b) + c) + 1) + 1);
}

uint64_t RecordCaseBody::conditional_body(const RecordCaseBody::Rec &r,
                                          bool flag) {
  uint64_t a = r.f1;
  uint64_t b = r.f2;
  uint64_t c = r.f3;
  if (flag) {
    if (a <= 0) {
      return b;
    } else {
      uint64_t _x = a - 1;
      return c;
    }
  } else {
    return (a + b);
  }
}

uint64_t RecordCaseBody::outer_ref(uint64_t x, const RecordCaseBody::Rec &r) {
  uint64_t a = r.f1;
  uint64_t b = r.f2;
  uint64_t c = r.f3;
  return (((x + a) + b) + c);
}

uint64_t RecordCaseBody::lambda_body(const RecordCaseBody::Rec &r, uint64_t n) {
  uint64_t a = r.f1;
  uint64_t b = r.f2;
  uint64_t c = r.f3;
  return (((n + a) + b) + c);
}

uint64_t RecordCaseBody::nested_record_match(const RecordCaseBody::RecRec &rr) {
  RecordCaseBody::Rec r = rr.inner;
  uint64_t n = rr.outer_field;
  uint64_t a = r.f1;
  uint64_t b = r.f2;
  uint64_t c = r.f3;
  return (((a + b) + c) + n);
}

uint64_t RecordCaseBody::global_in_body(const RecordCaseBody::Rec &r) {
  uint64_t a = r.f1;
  uint64_t b = r.f2;
  uint64_t c = r.f3;
  return (((global_const + a) + b) + c);
}

uint64_t RecordCaseBody::guarded_body(const RecordCaseBody::Rec &r) {
  uint64_t a = r.f1;
  uint64_t b = r.f2;
  uint64_t c = r.f3;
  if (a == UINT64_C(0)) {
    if (b == UINT64_C(0)) {
      return c;
    } else {
      return b;
    }
  } else {
    return a;
  }
}

RecordCaseBody::Rec
RecordCaseBody::constructor_body(const RecordCaseBody::Rec &r) {
  uint64_t a = r.f1;
  uint64_t b = r.f2;
  uint64_t c = r.f3;
  return Rec{(a + UINT64_C(1)), (b + UINT64_C(1)), (c + UINT64_C(1))};
}

uint64_t RecordCaseBody::sum_list(const RecordCaseBody::list<uint64_t> &l) {
  if (std::holds_alternative<typename RecordCaseBody::list<uint64_t>::Nil>(
          l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename RecordCaseBody::list<uint64_t>::Cons>(l.v());
    return (a0 + sum_list(*a1));
  }
}

uint64_t RecordCaseBody::list_in_body(const RecordCaseBody::Rec &r) {
  uint64_t a = r.f1;
  uint64_t b = r.f2;
  uint64_t c = r.f3;
  return sum_list(list<uint64_t>::cons(
      a,
      list<uint64_t>::cons(b, list<uint64_t>::cons(c, list<uint64_t>::nil()))));
}
