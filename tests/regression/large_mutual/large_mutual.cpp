#include <large_mutual.h>

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
LargeMutual::expr_size(const std::shared_ptr<LargeMutual::expr> &e) {
  return std::visit(
      Overloaded{
          [](const typename LargeMutual::expr::ENum _args) -> unsigned int {
            return 1u;
          },
          [](const typename LargeMutual::expr::EVar _args) -> unsigned int {
            return 1u;
          },
          [](const typename LargeMutual::expr::EAdd _args) -> unsigned int {
            std::shared_ptr<LargeMutual::expr> l = _args.d_a0;
            std::shared_ptr<LargeMutual::expr> r = _args.d_a1;
            return ((expr_size(std::move(l)) + expr_size(std::move(r))) + 1);
          },
          [](const typename LargeMutual::expr::EMul _args) -> unsigned int {
            std::shared_ptr<LargeMutual::expr> l = _args.d_a0;
            std::shared_ptr<LargeMutual::expr> r = _args.d_a1;
            return ((expr_size(std::move(l)) + expr_size(std::move(r))) + 1);
          },
          [](const typename LargeMutual::expr::ECond _args) -> unsigned int {
            std::shared_ptr<LargeMutual::bexpr> b = _args.d_a0;
            std::shared_ptr<LargeMutual::expr> t = _args.d_a1;
            std::shared_ptr<LargeMutual::expr> f = _args.d_a2;
            return (((bexpr_size(std::move(b)) + expr_size(std::move(t))) +
                     expr_size(std::move(f))) +
                    1);
          }},
      e->v());
}

__attribute__((pure)) unsigned int
LargeMutual::bexpr_size(const std::shared_ptr<LargeMutual::bexpr> &b) {
  return std::visit(
      Overloaded{
          [](const typename LargeMutual::bexpr::BTrue _args) -> unsigned int {
            return 1u;
          },
          [](const typename LargeMutual::bexpr::BFalse _args) -> unsigned int {
            return 1u;
          },
          [](const typename LargeMutual::bexpr::BEq _args) -> unsigned int {
            std::shared_ptr<LargeMutual::expr> l = _args.d_a0;
            std::shared_ptr<LargeMutual::expr> r = _args.d_a1;
            return ((expr_size(std::move(l)) + expr_size(std::move(r))) + 1);
          },
          [](const typename LargeMutual::bexpr::BLt _args) -> unsigned int {
            std::shared_ptr<LargeMutual::expr> l = _args.d_a0;
            std::shared_ptr<LargeMutual::expr> r = _args.d_a1;
            return ((expr_size(std::move(l)) + expr_size(std::move(r))) + 1);
          },
          [](const typename LargeMutual::bexpr::BAnd _args) -> unsigned int {
            std::shared_ptr<LargeMutual::bexpr> l = _args.d_a0;
            std::shared_ptr<LargeMutual::bexpr> r = _args.d_a1;
            return ((bexpr_size(std::move(l)) + bexpr_size(std::move(r))) + 1);
          },
          [](const typename LargeMutual::bexpr::BOr _args) -> unsigned int {
            std::shared_ptr<LargeMutual::bexpr> l = _args.d_a0;
            std::shared_ptr<LargeMutual::bexpr> r = _args.d_a1;
            return ((bexpr_size(std::move(l)) + bexpr_size(std::move(r))) + 1);
          },
          [](const typename LargeMutual::bexpr::BNot _args) -> unsigned int {
            std::shared_ptr<LargeMutual::bexpr> b0 = _args.d_a0;
            return (bexpr_size(std::move(b0)) + 1);
          }},
      b->v());
}

__attribute__((pure)) unsigned int
LargeMutual::stmt_size(const std::shared_ptr<LargeMutual::stmt> &s) {
  return std::visit(
      Overloaded{
          [](const typename LargeMutual::stmt::SAssign _args) -> unsigned int {
            std::shared_ptr<LargeMutual::expr> e = _args.d_a1;
            return (expr_size(std::move(e)) + 1);
          },
          [](const typename LargeMutual::stmt::SSeq _args) -> unsigned int {
            std::shared_ptr<LargeMutual::stmt> s1 = _args.d_a0;
            std::shared_ptr<LargeMutual::stmt> s2 = _args.d_a1;
            return ((stmt_size(std::move(s1)) + stmt_size(std::move(s2))) + 1);
          },
          [](const typename LargeMutual::stmt::SIf _args) -> unsigned int {
            std::shared_ptr<LargeMutual::bexpr> b = _args.d_a0;
            std::shared_ptr<LargeMutual::stmt> s1 = _args.d_a1;
            std::shared_ptr<LargeMutual::stmt> s2 = _args.d_a2;
            return (((bexpr_size(std::move(b)) + stmt_size(std::move(s1))) +
                     stmt_size(std::move(s2))) +
                    1);
          },
          [](const typename LargeMutual::stmt::SWhile _args) -> unsigned int {
            std::shared_ptr<LargeMutual::bexpr> b = _args.d_a0;
            std::shared_ptr<LargeMutual::stmt> body = _args.d_a1;
            return ((bexpr_size(std::move(b)) + stmt_size(std::move(body))) +
                    1);
          },
          [](const typename LargeMutual::stmt::SSkip _args) -> unsigned int {
            return 1u;
          }},
      s->v());
}
