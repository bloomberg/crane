#include <large_mutual.h>

__attribute__((pure)) unsigned int
LargeMutual::expr_size(const LargeMutual::expr &e) {
  if (std::holds_alternative<typename LargeMutual::expr::EAdd>(e.v())) {
    const auto &[d_a0, d_a1] =
        std::get<typename LargeMutual::expr::EAdd>(e.v());
    return ((expr_size(*(d_a0)) + expr_size(*(d_a1))) + 1);
  } else if (std::holds_alternative<typename LargeMutual::expr::EMul>(e.v())) {
    const auto &[d_a0, d_a1] =
        std::get<typename LargeMutual::expr::EMul>(e.v());
    return ((expr_size(*(d_a0)) + expr_size(*(d_a1))) + 1);
  } else if (std::holds_alternative<typename LargeMutual::expr::ECond>(e.v())) {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename LargeMutual::expr::ECond>(e.v());
    return (((bexpr_size(*(d_a0)) + expr_size(*(d_a1))) + expr_size(*(d_a2))) +
            1);
  } else {
    return 1u;
  }
}

__attribute__((pure)) unsigned int
LargeMutual::bexpr_size(const LargeMutual::bexpr &b) {
  if (std::holds_alternative<typename LargeMutual::bexpr::BEq>(b.v())) {
    const auto &[d_a0, d_a1] =
        std::get<typename LargeMutual::bexpr::BEq>(b.v());
    return ((expr_size(*(d_a0)) + expr_size(*(d_a1))) + 1);
  } else if (std::holds_alternative<typename LargeMutual::bexpr::BLt>(b.v())) {
    const auto &[d_a0, d_a1] =
        std::get<typename LargeMutual::bexpr::BLt>(b.v());
    return ((expr_size(*(d_a0)) + expr_size(*(d_a1))) + 1);
  } else if (std::holds_alternative<typename LargeMutual::bexpr::BAnd>(b.v())) {
    const auto &[d_a0, d_a1] =
        std::get<typename LargeMutual::bexpr::BAnd>(b.v());
    return ((bexpr_size(*(d_a0)) + bexpr_size(*(d_a1))) + 1);
  } else if (std::holds_alternative<typename LargeMutual::bexpr::BOr>(b.v())) {
    const auto &[d_a0, d_a1] =
        std::get<typename LargeMutual::bexpr::BOr>(b.v());
    return ((bexpr_size(*(d_a0)) + bexpr_size(*(d_a1))) + 1);
  } else if (std::holds_alternative<typename LargeMutual::bexpr::BNot>(b.v())) {
    const auto &[d_a0] = std::get<typename LargeMutual::bexpr::BNot>(b.v());
    return (bexpr_size(*(d_a0)) + 1);
  } else {
    return 1u;
  }
}

__attribute__((pure)) unsigned int
LargeMutual::stmt_size(const LargeMutual::stmt &s) {
  if (std::holds_alternative<typename LargeMutual::stmt::SAssign>(s.v())) {
    const auto &[d_a0, d_a1] =
        std::get<typename LargeMutual::stmt::SAssign>(s.v());
    return (expr_size(*(d_a1)) + 1);
  } else if (std::holds_alternative<typename LargeMutual::stmt::SSeq>(s.v())) {
    const auto &[d_a0, d_a1] =
        std::get<typename LargeMutual::stmt::SSeq>(s.v());
    return ((stmt_size(*(d_a0)) + stmt_size(*(d_a1))) + 1);
  } else if (std::holds_alternative<typename LargeMutual::stmt::SIf>(s.v())) {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename LargeMutual::stmt::SIf>(s.v());
    return (((bexpr_size(*(d_a0)) + stmt_size(*(d_a1))) + stmt_size(*(d_a2))) +
            1);
  } else if (std::holds_alternative<typename LargeMutual::stmt::SWhile>(
                 s.v())) {
    const auto &[d_a0, d_a1] =
        std::get<typename LargeMutual::stmt::SWhile>(s.v());
    return ((bexpr_size(*(d_a0)) + stmt_size(*(d_a1))) + 1);
  } else {
    return 1u;
  }
}
