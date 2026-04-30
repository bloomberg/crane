#include <record_case_body.h>

unsigned int RecordCaseBody::case_in_body(const RecordCaseBody::Rec &r) {
  unsigned int a = r.f1;
  unsigned int b = r.f2;
  unsigned int c = r.f3;
  if (a <= 0) {
    return (b + c);
  } else {
    unsigned int n = a - 1;
    return ((n + b) + c);
  }
}

unsigned int RecordCaseBody::helper(const unsigned int &n) {
  if (n <= 0) {
    return 0u;
  } else {
    unsigned int n_ = n - 1;
    return (n + helper(n_));
  }
}

unsigned int RecordCaseBody::fix_in_body(const RecordCaseBody::Rec &r) {
  unsigned int a = r.f1;
  unsigned int b = r.f2;
  unsigned int c = r.f3;
  return helper(((a + b) + c));
}

unsigned int RecordCaseBody::let_in_body(const RecordCaseBody::Rec &r) {
  unsigned int a = r.f1;
  unsigned int b = r.f2;
  unsigned int c = r.f3;
  unsigned int x = (a + b);
  unsigned int y = (x + c);
  unsigned int z = (y * 2u);
  if (z <= 0) {
    return 0u;
  } else {
    unsigned int _x = z - 1;
    return z;
  }
}

unsigned int RecordCaseBody::apply_nonfld(const RecordCaseBody::Rec &r) {
  unsigned int a = r.f1;
  unsigned int b = r.f2;
  unsigned int c = r.f3;
  return ((((a + b) + c) + 1) + 1);
}

unsigned int RecordCaseBody::conditional_body(const RecordCaseBody::Rec &r,
                                              const bool &flag) {
  unsigned int a = r.f1;
  unsigned int b = r.f2;
  unsigned int c = r.f3;
  if (flag) {
    if (a <= 0) {
      return b;
    } else {
      unsigned int _x = a - 1;
      return c;
    }
  } else {
    return (a + b);
  }
}

unsigned int RecordCaseBody::outer_ref(const unsigned int &x,
                                       const RecordCaseBody::Rec &r) {
  unsigned int a = r.f1;
  unsigned int b = r.f2;
  unsigned int c = r.f3;
  return (((x + a) + b) + c);
}

unsigned int RecordCaseBody::lambda_body(const RecordCaseBody::Rec &r,
                                         const unsigned int &n) {
  unsigned int a = r.f1;
  unsigned int b = r.f2;
  unsigned int c = r.f3;
  return (((n + a) + b) + c);
}

unsigned int
RecordCaseBody::nested_record_match(const RecordCaseBody::RecRec &rr) {
  RecordCaseBody::Rec r = rr.inner;
  unsigned int n = rr.outer_field;
  unsigned int a = r.f1;
  unsigned int b = r.f2;
  unsigned int c = r.f3;
  return (((a + b) + c) + n);
}

unsigned int RecordCaseBody::global_in_body(const RecordCaseBody::Rec &r) {
  unsigned int a = r.f1;
  unsigned int b = r.f2;
  unsigned int c = r.f3;
  return (((global_const + a) + b) + c);
}

unsigned int RecordCaseBody::guarded_body(const RecordCaseBody::Rec &r) {
  unsigned int a = r.f1;
  unsigned int b = r.f2;
  unsigned int c = r.f3;
  if (a == 0u) {
    if (b == 0u) {
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
  unsigned int a = r.f1;
  unsigned int b = r.f2;
  unsigned int c = r.f3;
  return Rec{(a + 1u), (b + 1u), (c + 1u)};
}

unsigned int
RecordCaseBody::sum_list(const RecordCaseBody::list<unsigned int> &l) {
  if (std::holds_alternative<typename RecordCaseBody::list<unsigned int>::Nil>(
          l.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename RecordCaseBody::list<unsigned int>::Cons>(l.v());
    return (d_a0 + sum_list(*(d_a1)));
  }
}

unsigned int RecordCaseBody::list_in_body(const RecordCaseBody::Rec &r) {
  unsigned int a = r.f1;
  unsigned int b = r.f2;
  unsigned int c = r.f3;
  return sum_list(list<unsigned int>::cons(
      a, list<unsigned int>::cons(
             b, list<unsigned int>::cons(c, list<unsigned int>::nil()))));
}
