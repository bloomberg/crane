// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_expr_variants.h>

namespace {
int testStatus = 0;
void aSsErT(bool condition, const char *message, int line) {
  if (condition) {
    std::cout << "Error " __FILE__ "(" << line << "): " << message
              << "    (failed)" << std::endl;
    if (0 <= testStatus && testStatus <= 100)
      ++testStatus;
  }
}
} // namespace
#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

using LE = LoopifyExprVariants;

// Helper to compare List<unsigned int> with an initializer list
bool list_eq(const std::shared_ptr<List<unsigned int>> &l,
             std::initializer_list<unsigned int> expected) {
  auto it = expected.begin();
  auto cur = l;
  while (it != expected.end()) {
    auto &v = cur->v();
    if (auto *cons = std::get_if<List<unsigned int>::Cons>(&v)) {
      if (cons->d_a0 != *it)
        return false;
      cur = cons->d_a1;
      ++it;
    } else {
      return false; // list too short
    }
  }
  // cur should be Nil
  return std::holds_alternative<List<unsigned int>::Nil>(cur->v());
}

bool list_empty(const std::shared_ptr<List<unsigned int>> &l) {
  return std::holds_alternative<List<unsigned int>::Nil>(l->v());
}

int main() {
  // eval_cond
  auto lit5 = LE::cond_expr::ctor::Lit_(5);
  auto lit3 = LE::cond_expr::ctor::Lit_(3);
  auto lit0 = LE::cond_expr::ctor::Lit_(0);

  ASSERT(lit5->eval_cond() == 5);

  auto sum = LE::cond_expr::ctor::Add_(lit5, lit3);
  ASSERT(sum->eval_cond() == 8);

  auto cond_true = LE::cond_expr::ctor::Cond_(lit5, lit3, lit0);
  ASSERT(cond_true->eval_cond() == 3);

  auto cond_false = LE::cond_expr::ctor::Cond_(lit0, lit5, lit3);
  ASSERT(cond_false->eval_cond() == 3);

  // size_cond
  auto lit = LE::cond_expr::ctor::Lit_(5);
  ASSERT(lit->size_cond() == 1);

  auto sum1 = LE::cond_expr::ctor::Add_(lit, lit);
  ASSERT(sum1->size_cond() == 3);

  auto cond = LE::cond_expr::ctor::Cond_(lit, lit, lit);
  ASSERT(cond->size_cond() == 4);

  // eval_arith
  auto n5 = LE::arith_expr::ctor::ANum_(5);
  auto n3 = LE::arith_expr::ctor::ANum_(3);
  auto n0 = LE::arith_expr::ctor::ANum_(0);

  ASSERT(n5->eval_arith() == 5);

  auto sum2 = LE::arith_expr::ctor::AAdd_(n5, n3);
  ASSERT(sum2->eval_arith() == 8);

  auto mul = LE::arith_expr::ctor::AMul_(n5, n3);
  ASSERT(mul->eval_arith() == 15);

  auto div = LE::arith_expr::ctor::ADiv_(n5, n3);
  ASSERT(div->eval_arith() == 1);

  auto div_zero = LE::arith_expr::ctor::ADiv_(n5, n0);
  ASSERT(div_zero->eval_arith() == 0);

  // count_ops
  auto num = LE::arith_expr::ctor::ANum_(5);
  ASSERT(num->count_ops() == 0);

  auto add = LE::arith_expr::ctor::AAdd_(num, num);
  ASSERT(add->count_ops() == 1);

  auto mul1 = LE::arith_expr::ctor::AMul_(num, num);
  auto complex = LE::arith_expr::ctor::AAdd_(add, mul1);
  ASSERT(complex->count_ops() == 3);

  // eval_bool
  auto t = LE::bool_expr::ctor::BTrue_();
  auto f = LE::bool_expr::ctor::BFalse_();

  ASSERT(t->eval_bool() == true);
  ASSERT(f->eval_bool() == false);

  auto and_expr = LE::bool_expr::ctor::BAnd_(t, f);
  ASSERT(and_expr->eval_bool() == false);

  auto or_expr = LE::bool_expr::ctor::BOr_(t, f);
  ASSERT(or_expr->eval_bool() == true);

  auto not_expr = LE::bool_expr::ctor::BNot_(f);
  ASSERT(not_expr->eval_bool() == true);

  // simplify_bool
  // And with false => false
  auto and_f = LE::bool_expr::ctor::BAnd_(t, f);
  ASSERT(and_f->simplify_bool()->eval_bool() == false);

  // Or with true => true
  auto or_t = LE::bool_expr::ctor::BOr_(t, f);
  ASSERT(or_t->simplify_bool()->eval_bool() == true);

  // Not(Not(x)) => x (via double negation)
  auto not_not_t = LE::bool_expr::ctor::BNot_(LE::bool_expr::ctor::BNot_(t));
  ASSERT(not_not_t->simplify_bool()->eval_bool() == true);

  // eval_list
  auto nil = LE::list_expr::ctor::LNil_();
  ASSERT(list_empty(nil->eval_list()));

  auto cons = LE::list_expr::ctor::LCons_(1,
    LE::list_expr::ctor::LCons_(2,
      LE::list_expr::ctor::LCons_(3, nil)));
  ASSERT(list_eq(cons->eval_list(), {1, 2, 3}));

  auto rep = LE::list_expr::ctor::LReplicate_(3, 5);
  ASSERT(list_eq(rep->eval_list(), {5, 5, 5}));

  auto l1 = LE::list_expr::ctor::LCons_(1, nil);
  auto l2 = LE::list_expr::ctor::LCons_(2, nil);
  auto app = LE::list_expr::ctor::LAppend_(l1, l2);
  ASSERT(list_eq(app->eval_list(), {1, 2}));

  // list_expr_size
  ASSERT(nil->list_expr_size() == 1);

  auto cons1 = LE::list_expr::ctor::LCons_(1,
    LE::list_expr::ctor::LCons_(2, nil));
  ASSERT(cons1->list_expr_size() == 3);

  auto rep1 = LE::list_expr::ctor::LReplicate_(10, 5);
  ASSERT(rep1->list_expr_size() == 1);

  auto app1 = LE::list_expr::ctor::LAppend_(cons1, nil);
  ASSERT(app1->list_expr_size() == 5);

  if (testStatus > 0) {
    std::cerr << "Error: " << testStatus << " test(s) failed." << std::endl;
    return testStatus;
  }
  return 0;
}
