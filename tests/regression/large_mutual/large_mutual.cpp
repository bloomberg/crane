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
            return ((expr_size(_args.d_a0) + expr_size(_args.d_a1)) + 1);
          },
          [](const typename LargeMutual::expr::EMul _args) -> unsigned int {
            return ((expr_size(_args.d_a0) + expr_size(_args.d_a1)) + 1);
          },
          [](const typename LargeMutual::expr::ECond _args) -> unsigned int {
            return (((bexpr_size(_args.d_a0) + expr_size(_args.d_a1)) +
                     expr_size(_args.d_a2)) +
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
            return ((expr_size(_args.d_a0) + expr_size(_args.d_a1)) + 1);
          },
          [](const typename LargeMutual::bexpr::BLt _args) -> unsigned int {
            return ((expr_size(_args.d_a0) + expr_size(_args.d_a1)) + 1);
          },
          [](const typename LargeMutual::bexpr::BAnd _args) -> unsigned int {
            return ((bexpr_size(_args.d_a0) + bexpr_size(_args.d_a1)) + 1);
          },
          [](const typename LargeMutual::bexpr::BOr _args) -> unsigned int {
            return ((bexpr_size(_args.d_a0) + bexpr_size(_args.d_a1)) + 1);
          },
          [](const typename LargeMutual::bexpr::BNot _args) -> unsigned int {
            return (bexpr_size(_args.d_a0) + 1);
          }},
      b->v());
}

__attribute__((pure)) unsigned int
LargeMutual::stmt_size(const std::shared_ptr<LargeMutual::stmt> &s) {
  return std::visit(
      Overloaded{
          [](const typename LargeMutual::stmt::SAssign _args) -> unsigned int {
            return (expr_size(_args.d_a1) + 1);
          },
          [](const typename LargeMutual::stmt::SSeq _args) -> unsigned int {
            return ((stmt_size(_args.d_a0) + stmt_size(_args.d_a1)) + 1);
          },
          [](const typename LargeMutual::stmt::SIf _args) -> unsigned int {
            return (((bexpr_size(_args.d_a0) + stmt_size(_args.d_a1)) +
                     stmt_size(_args.d_a2)) +
                    1);
          },
          [](const typename LargeMutual::stmt::SWhile _args) -> unsigned int {
            return ((bexpr_size(_args.d_a0) + stmt_size(_args.d_a1)) + 1);
          },
          [](const typename LargeMutual::stmt::SSkip _args) -> unsigned int {
            return 1u;
          }},
      s->v());
}
