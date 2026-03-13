#include <record_case_body.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

__attribute__((pure)) unsigned int
RecordCaseBody::case_in_body(const std::shared_ptr<RecordCaseBody::Rec> &r) {
  return [&](void) {
    unsigned int a = r->f1;
    unsigned int b = r->f2;
    unsigned int c = r->f3;
    if (a <= 0) {
      return (b + c);
    } else {
      unsigned int n = a - 1;
      return ((n + b) + c);
    }
  }();
}

__attribute__((pure)) unsigned int
RecordCaseBody::helper(const unsigned int n) {
  if (n <= 0) {
    return 0u;
  } else {
    unsigned int n_ = n - 1;
    return (n + helper(n_));
  }
}

__attribute__((pure)) unsigned int
RecordCaseBody::fix_in_body(const std::shared_ptr<RecordCaseBody::Rec> &r) {
  return [&](void) {
    unsigned int a = r->f1;
    unsigned int b = r->f2;
    unsigned int c = r->f3;
    return helper(((a + b) + c));
  }();
}

__attribute__((pure)) unsigned int
RecordCaseBody::let_in_body(const std::shared_ptr<RecordCaseBody::Rec> &r) {
  return [&](void) {
    unsigned int a = r->f1;
    unsigned int b = r->f2;
    unsigned int c = r->f3;
    unsigned int x = (a + b);
    unsigned int y = (std::move(x) + c);
    unsigned int z = (std::move(y) * 2u);
    if (z <= 0) {
      return 0u;
    } else {
      unsigned int _x = z - 1;
      return std::move(z);
    }
  }();
}

__attribute__((pure)) unsigned int
RecordCaseBody::apply_nonfld(const std::shared_ptr<RecordCaseBody::Rec> &r) {
  return [&](void) {
    unsigned int a = r->f1;
    unsigned int b = r->f2;
    unsigned int c = r->f3;
    return ((((a + b) + c) + 1) + 1);
  }();
}

__attribute__((pure)) unsigned int
RecordCaseBody::conditional_body(const std::shared_ptr<RecordCaseBody::Rec> &r,
                                 const bool flag) {
  return [&](void) {
    unsigned int a = r->f1;
    unsigned int b = r->f2;
    unsigned int c = r->f3;
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
  }();
}

__attribute__((pure)) unsigned int
RecordCaseBody::outer_ref(const unsigned int x,
                          const std::shared_ptr<RecordCaseBody::Rec> &r) {
  return [&](void) {
    unsigned int a = r->f1;
    unsigned int b = r->f2;
    unsigned int c = r->f3;
    return (((x + a) + b) + c);
  }();
}

__attribute__((pure)) unsigned int
RecordCaseBody::lambda_body(const std::shared_ptr<RecordCaseBody::Rec> &r,
                            const unsigned int n) {
  return [&](void) {
    unsigned int a = r->f1;
    unsigned int b = r->f2;
    unsigned int c = r->f3;
    return (((n + a) + b) + c);
  }();
}

__attribute__((pure)) unsigned int RecordCaseBody::nested_record_match(
    const std::shared_ptr<RecordCaseBody::RecRec> &rr) {
  return [&](void) {
    std::shared_ptr<RecordCaseBody::Rec> r = rr->inner;
    unsigned int n = rr->outer_field;
    return [&](void) {
      unsigned int a = r->f1;
      unsigned int b = r->f2;
      unsigned int c = r->f3;
      return (((a + b) + c) + n);
    }();
  }();
}

__attribute__((pure)) unsigned int
RecordCaseBody::global_in_body(const std::shared_ptr<RecordCaseBody::Rec> &r) {
  return [&](void) {
    unsigned int a = r->f1;
    unsigned int b = r->f2;
    unsigned int c = r->f3;
    return (((global_const + a) + b) + c);
  }();
}

__attribute__((pure)) unsigned int
RecordCaseBody::guarded_body(const std::shared_ptr<RecordCaseBody::Rec> &r) {
  return [&](void) {
    unsigned int a = r->f1;
    unsigned int b = r->f2;
    unsigned int c = r->f3;
    if (a == 0u) {
      if (b == 0u) {
        return c;
      } else {
        return b;
      }
    } else {
      return a;
    }
  }();
}

std::shared_ptr<RecordCaseBody::Rec> RecordCaseBody::constructor_body(
    const std::shared_ptr<RecordCaseBody::Rec> &r) {
  return [&](void) {
    unsigned int a = r->f1;
    unsigned int b = r->f2;
    unsigned int c = r->f3;
    return std::make_shared<RecordCaseBody::Rec>(
        Rec{(a + 1u), (b + 1u), (c + 1u)});
  }();
}

__attribute__((pure)) unsigned int RecordCaseBody::sum_list(
    const std::shared_ptr<RecordCaseBody::list<unsigned int>> &l) {
  return std::visit(
      Overloaded{
          [](const typename RecordCaseBody::list<unsigned int>::Nil _args)
              -> unsigned int { return 0u; },
          [](const typename RecordCaseBody::list<unsigned int>::Cons _args)
              -> unsigned int {
            unsigned int x = _args.d_a0;
            std::shared_ptr<RecordCaseBody::list<unsigned int>> xs = _args.d_a1;
            return (std::move(x) + sum_list(std::move(xs)));
          }},
      l->v());
}

__attribute__((pure)) unsigned int
RecordCaseBody::list_in_body(const std::shared_ptr<RecordCaseBody::Rec> &r) {
  return [&](void) {
    unsigned int a = r->f1;
    unsigned int b = r->f2;
    unsigned int c = r->f3;
    return sum_list(list<unsigned int>::ctor::Cons_(
        a, list<unsigned int>::ctor::Cons_(
               b, list<unsigned int>::ctor::Cons_(
                      c, list<unsigned int>::ctor::Nil_()))));
  }();
}
