#include <large_mutual.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
LargeMutual::expr_size(const std::shared_ptr<LargeMutual::expr> &e) {
  if (std::holds_alternative<typename LargeMutual::expr::EAdd>(e->v())) {
    const auto &_m = *std::get_if<typename LargeMutual::expr::EAdd>(&e->v());
    return ((expr_size(_m.d_a0) + expr_size(_m.d_a1)) + 1);
  } else if (std::holds_alternative<typename LargeMutual::expr::EMul>(e->v())) {
    const auto &_m = *std::get_if<typename LargeMutual::expr::EMul>(&e->v());
    return ((expr_size(_m.d_a0) + expr_size(_m.d_a1)) + 1);
  } else if (std::holds_alternative<typename LargeMutual::expr::ECond>(
                 e->v())) {
    const auto &_m = *std::get_if<typename LargeMutual::expr::ECond>(&e->v());
    return (((bexpr_size(_m.d_a0) + expr_size(_m.d_a1)) + expr_size(_m.d_a2)) +
            1);
  } else {
    return 1u;
  }
}

__attribute__((pure)) unsigned int
LargeMutual::bexpr_size(const std::shared_ptr<LargeMutual::bexpr> &b) {
  if (std::holds_alternative<typename LargeMutual::bexpr::BEq>(b->v())) {
    const auto &_m = *std::get_if<typename LargeMutual::bexpr::BEq>(&b->v());
    return ((expr_size(_m.d_a0) + expr_size(_m.d_a1)) + 1);
  } else if (std::holds_alternative<typename LargeMutual::bexpr::BLt>(b->v())) {
    const auto &_m = *std::get_if<typename LargeMutual::bexpr::BLt>(&b->v());
    return ((expr_size(_m.d_a0) + expr_size(_m.d_a1)) + 1);
  } else if (std::holds_alternative<typename LargeMutual::bexpr::BAnd>(
                 b->v())) {
    const auto &_m = *std::get_if<typename LargeMutual::bexpr::BAnd>(&b->v());
    return ((bexpr_size(_m.d_a0) + bexpr_size(_m.d_a1)) + 1);
  } else if (std::holds_alternative<typename LargeMutual::bexpr::BOr>(b->v())) {
    const auto &_m = *std::get_if<typename LargeMutual::bexpr::BOr>(&b->v());
    return ((bexpr_size(_m.d_a0) + bexpr_size(_m.d_a1)) + 1);
  } else if (std::holds_alternative<typename LargeMutual::bexpr::BNot>(
                 b->v())) {
    const auto &_m = *std::get_if<typename LargeMutual::bexpr::BNot>(&b->v());
    return (bexpr_size(_m.d_a0) + 1);
  } else {
    return 1u;
  }
}

__attribute__((pure)) unsigned int
LargeMutual::stmt_size(const std::shared_ptr<LargeMutual::stmt> &s) {
  if (std::holds_alternative<typename LargeMutual::stmt::SAssign>(s->v())) {
    const auto &_m = *std::get_if<typename LargeMutual::stmt::SAssign>(&s->v());
    return (expr_size(_m.d_a1) + 1);
  } else if (std::holds_alternative<typename LargeMutual::stmt::SSeq>(s->v())) {
    const auto &_m = *std::get_if<typename LargeMutual::stmt::SSeq>(&s->v());
    return ((stmt_size(_m.d_a0) + stmt_size(_m.d_a1)) + 1);
  } else if (std::holds_alternative<typename LargeMutual::stmt::SIf>(s->v())) {
    const auto &_m = *std::get_if<typename LargeMutual::stmt::SIf>(&s->v());
    return (((bexpr_size(_m.d_a0) + stmt_size(_m.d_a1)) + stmt_size(_m.d_a2)) +
            1);
  } else if (std::holds_alternative<typename LargeMutual::stmt::SWhile>(
                 s->v())) {
    const auto &_m = *std::get_if<typename LargeMutual::stmt::SWhile>(&s->v());
    return ((bexpr_size(_m.d_a0) + stmt_size(_m.d_a1)) + 1);
  } else {
    return 1u;
  }
}
