#include <where_clause.h>

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
WhereClause::eval(const std::shared_ptr<WhereClause::Expr> &e) {
  return std::visit(
      Overloaded{
          [](const typename WhereClause::Expr::Num _args) -> unsigned int {
            return _args.d_a0;
          },
          [](const typename WhereClause::Expr::Plus _args) -> unsigned int {
            return (eval(_args.d_a0) + eval(_args.d_a1));
          },
          [](const typename WhereClause::Expr::Times _args) -> unsigned int {
            return (eval(_args.d_a0) * eval(_args.d_a1));
          }},
      e->v());
}

__attribute__((pure)) unsigned int
WhereClause::expr_size(const std::shared_ptr<WhereClause::Expr> &e) {
  return std::visit(
      Overloaded{
          [](const typename WhereClause::Expr::Num _args) -> unsigned int {
            return 1u;
          },
          [](const typename WhereClause::Expr::Plus _args) -> unsigned int {
            return ((1u + expr_size(_args.d_a0)) + expr_size(_args.d_a1));
          },
          [](const typename WhereClause::Expr::Times _args) -> unsigned int {
            return ((1u + expr_size(_args.d_a0)) + expr_size(_args.d_a1));
          }},
      e->v());
}

__attribute__((pure)) bool
WhereClause::beval(const std::shared_ptr<WhereClause::BExpr> &e) {
  return std::visit(
      Overloaded{[](const typename WhereClause::BExpr::BTrue _args) -> bool {
                   return true;
                 },
                 [](const typename WhereClause::BExpr::BFalse _args) -> bool {
                   return false;
                 },
                 [](const typename WhereClause::BExpr::BAnd _args) -> bool {
                   return (beval(_args.d_a0) && beval(_args.d_a1));
                 },
                 [](const typename WhereClause::BExpr::BOr _args) -> bool {
                   return (beval(_args.d_a0) || beval(_args.d_a1));
                 },
                 [](const typename WhereClause::BExpr::BNot _args) -> bool {
                   return !(beval(_args.d_a0));
                 }},
      e->v());
}

__attribute__((pure)) unsigned int
WhereClause::aeval(const std::shared_ptr<WhereClause::AExpr> &e) {
  return std::visit(
      Overloaded{
          [](const typename WhereClause::AExpr::ANum _args) -> unsigned int {
            return _args.d_a0;
          },
          [](const typename WhereClause::AExpr::APlus _args) -> unsigned int {
            return (aeval(_args.d_a0) + aeval(_args.d_a1));
          },
          [](const typename WhereClause::AExpr::AIf _args) -> unsigned int {
            if (beval(_args.d_a0)) {
              return aeval(_args.d_a1);
            } else {
              return aeval(_args.d_a2);
            }
          }},
      e->v());
}
