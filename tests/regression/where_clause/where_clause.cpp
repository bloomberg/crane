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
            unsigned int n = _args.d_a0;
            return std::move(n);
          },
          [](const typename WhereClause::Expr::Plus _args) -> unsigned int {
            std::shared_ptr<WhereClause::Expr> a = _args.d_a0;
            std::shared_ptr<WhereClause::Expr> b = _args.d_a1;
            return (eval(std::move(a)) + eval(std::move(b)));
          },
          [](const typename WhereClause::Expr::Times _args) -> unsigned int {
            std::shared_ptr<WhereClause::Expr> a = _args.d_a0;
            std::shared_ptr<WhereClause::Expr> b = _args.d_a1;
            return (eval(std::move(a)) * eval(std::move(b)));
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
            std::shared_ptr<WhereClause::Expr> a = _args.d_a0;
            std::shared_ptr<WhereClause::Expr> b = _args.d_a1;
            return ((1u + expr_size(std::move(a))) + expr_size(std::move(b)));
          },
          [](const typename WhereClause::Expr::Times _args) -> unsigned int {
            std::shared_ptr<WhereClause::Expr> a = _args.d_a0;
            std::shared_ptr<WhereClause::Expr> b = _args.d_a1;
            return ((1u + expr_size(std::move(a))) + expr_size(std::move(b)));
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
                   std::shared_ptr<WhereClause::BExpr> a = _args.d_a0;
                   std::shared_ptr<WhereClause::BExpr> b = _args.d_a1;
                   return (beval(std::move(a)) && beval(std::move(b)));
                 },
                 [](const typename WhereClause::BExpr::BOr _args) -> bool {
                   std::shared_ptr<WhereClause::BExpr> a = _args.d_a0;
                   std::shared_ptr<WhereClause::BExpr> b = _args.d_a1;
                   return (beval(std::move(a)) || beval(std::move(b)));
                 },
                 [](const typename WhereClause::BExpr::BNot _args) -> bool {
                   std::shared_ptr<WhereClause::BExpr> a = _args.d_a0;
                   return !(beval(std::move(a)));
                 }},
      e->v());
}

__attribute__((pure)) unsigned int
WhereClause::aeval(const std::shared_ptr<WhereClause::AExpr> &e) {
  return std::visit(
      Overloaded{
          [](const typename WhereClause::AExpr::ANum _args) -> unsigned int {
            unsigned int n = _args.d_a0;
            return std::move(n);
          },
          [](const typename WhereClause::AExpr::APlus _args) -> unsigned int {
            std::shared_ptr<WhereClause::AExpr> a = _args.d_a0;
            std::shared_ptr<WhereClause::AExpr> b = _args.d_a1;
            return (aeval(std::move(a)) + aeval(std::move(b)));
          },
          [](const typename WhereClause::AExpr::AIf _args) -> unsigned int {
            std::shared_ptr<WhereClause::BExpr> c = _args.d_a0;
            std::shared_ptr<WhereClause::AExpr> t = _args.d_a1;
            std::shared_ptr<WhereClause::AExpr> f = _args.d_a2;
            if (beval(std::move(c))) {
              return aeval(std::move(t));
            } else {
              return aeval(std::move(f));
            }
          }},
      e->v());
}
