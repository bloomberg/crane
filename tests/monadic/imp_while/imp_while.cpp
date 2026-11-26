#include "imp_while.h"

/// The value of e, the variables read from vars.
uint64_t eval(STRefs r, std::span<const uint64_t> vars, const Expr &e) {
  if (std::holds_alternative<typename Expr::Num>(e.v())) {
    const auto &[n0] = std::get<typename Expr::Num>(e.v());
    return n0;
  } else if (std::holds_alternative<typename Expr::Var>(e.v())) {
    const auto &[x0] = std::get<typename Expr::Var>(e.v());
    return vars[x0];
  } else if (std::holds_alternative<typename Expr::Add>(e.v())) {
    const auto &[a0, b0] = std::get<typename Expr::Add>(e.v());
    uint64_t x = eval(r, vars, *a0);
    uint64_t y = eval(r, vars, *b0);
    return (x + y);
  } else if (std::holds_alternative<typename Expr::Sub>(e.v())) {
    const auto &[a0, b0] = std::get<typename Expr::Sub>(e.v());
    uint64_t x = eval(r, vars, *a0);
    uint64_t y = eval(r, vars, *b0);
    return (((x - y) > x ? 0 : (x - y)));
  } else if (std::holds_alternative<typename Expr::Mul>(e.v())) {
    const auto &[a0, b0] = std::get<typename Expr::Mul>(e.v());
    uint64_t x = eval(r, vars, *a0);
    uint64_t y = eval(r, vars, *b0);
    return (x * y);
  } else {
    const auto &[a0, b0] = std::get<typename Expr::Lt>(e.v());
    uint64_t x = eval(r, vars, *a0);
    uint64_t y = eval(r, vars, *b0);
    return (x < y ? UINT64_C(1) : UINT64_C(0));
  }
}

/// One statement: its substatements are run by call.
uint64_t exec_body(STRefs r, std::span<uint64_t> vars, const Stmt &s) {
  if (std::holds_alternative<typename Stmt::Skip>(s.v())) {
    return UINT64_C(1);
  } else if (std::holds_alternative<typename Stmt::Assign>(s.v())) {
    const auto &[x0, e0] = std::get<typename Stmt::Assign>(s.v());
    uint64_t v = eval(r, std::span<const uint64_t>{vars}, e0);
    vars[x0] = v;
    return UINT64_C(1);
  } else if (std::holds_alternative<typename Stmt::Seq>(s.v())) {
    const auto &[s3, s4] = std::get<typename Stmt::Seq>(s.v());
    uint64_t n1 = crane::rec_call<Stmt, uint64_t>(*s3);
    uint64_t n2 = crane::rec_call<Stmt, uint64_t>(*s4);
    return (n1 + n2);
  } else if (std::holds_alternative<typename Stmt::If>(s.v())) {
    const auto &[c0, s3, s4] = std::get<typename Stmt::If>(s.v());
    uint64_t v = eval(r, std::span<const uint64_t>{vars}, c0);
    uint64_t n = (v == UINT64_C(0) ? crane::rec_call<Stmt, uint64_t>(*s4)
                                   : crane::rec_call<Stmt, uint64_t>(*s3));
    return (n + 1);
  } else {
    const auto &[c0, body0] = std::get<typename Stmt::While>(s.v());
    uint64_t v = eval(r, std::span<const uint64_t>{vars}, c0);
    if (v == UINT64_C(0)) {
      return UINT64_C(1);
    } else {
      uint64_t n1 = crane::rec_call<Stmt, uint64_t>(*body0);
      uint64_t n2 = crane::rec_call<Stmt, uint64_t>(
          Stmt::While_(c0, crane::shared_child(body0)));
      return ((n1 + n2) + 1);
    }
  }
}

uint64_t exec(STRefs r,
              const std::shared_ptr<crane::array_storage<uint64_t>> &vars,
              const Stmt &s) {
  return crane::rec<Stmt, uint64_t>([=](Stmt _x0) -> uint64_t {
    return exec_body(r, std::span<uint64_t>{*vars}, _x0);
  },
                                    s);
}

/// Runs s on n variables, all 0: the steps it took and the final
/// variables.
std::pair<uint64_t, List<uint64_t>> run(STRefs r, uint64_t n, const Stmt &s) {
  std::shared_ptr<crane::array_storage<uint64_t>> vars =
      std::make_shared<crane::array_storage<uint64_t>>(crane::st::extent(n),
                                                       UINT64_C(0));
  uint64_t steps = exec(r, vars, s);
  List<uint64_t> vs =
      crane::st::elems<List<uint64_t>>(std::span<const uint64_t>{*vars});
  return std::make_pair(steps, std::move(vs));
}

/// x1 := k!, counting x0 down from k.
Stmt factorial(uint64_t k) {
  return Stmt::seq(Stmt::assign(UINT64_C(0), Expr::num(k)),
                   Stmt::seq(
                       Stmt::assign(UINT64_C(1), Expr::num(UINT64_C(1))),
                       Stmt::While_(Expr::lt(Expr::num(UINT64_C(0)),
                                             Expr::var(UINT64_C(0))),
                                    Stmt::seq(
                                        Stmt::assign(
                                            UINT64_C(1),
                                            Expr::mul(Expr::var(UINT64_C(1)),
                                                      Expr::var(UINT64_C(0)))),
                                        Stmt::assign(
                                            UINT64_C(0),
                                            Expr::sub(Expr::var(UINT64_C(0)),
                                                      Expr::num(UINT64_C(1))))))));
}

/// x1 := fib k, counting x0 down from k with (x1, x2) := (x2, x1 + x2).
Stmt fibonacci(uint64_t k) {
  return Stmt::seq(
      Stmt::assign(UINT64_C(0), Expr::num(k)),
      Stmt::seq(
          Stmt::assign(UINT64_C(1), Expr::num(UINT64_C(0))),
          Stmt::seq(Stmt::assign(UINT64_C(2), Expr::num(UINT64_C(1))),
                    Stmt::While_(
                        Expr::lt(Expr::num(UINT64_C(0)),
                                 Expr::var(UINT64_C(0))),
                        Stmt::seq(
                            Stmt::assign(UINT64_C(3),
                                         Expr::add(Expr::var(UINT64_C(1)),
                                                   Expr::var(UINT64_C(2)))),
                            Stmt::seq(
                                Stmt::assign(UINT64_C(1),
                                             Expr::var(UINT64_C(2))),
                                Stmt::seq(
                                    Stmt::assign(UINT64_C(2),
                                                 Expr::var(UINT64_C(3))),
                                    Stmt::assign(
                                        UINT64_C(0),
                                        Expr::sub(Expr::var(UINT64_C(0)),
                                                  Expr::num(UINT64_C(1)))))))))));
}

/// A nested loop: x2 := k * k, one increment at a time.
Stmt square(uint64_t k) {
  return Stmt::seq(
      Stmt::assign(UINT64_C(0), Expr::num(k)),
      Stmt::While_(
          Expr::lt(Expr::num(UINT64_C(0)), Expr::var(UINT64_C(0))),
          Stmt::seq(
              Stmt::assign(UINT64_C(1), Expr::num(k)),
              Stmt::seq(
                  Stmt::While_(
                      Expr::lt(Expr::num(UINT64_C(0)), Expr::var(UINT64_C(1))),
                      Stmt::seq(
                          Stmt::assign(UINT64_C(2),
                                       Expr::add(Expr::var(UINT64_C(2)),
                                                 Expr::num(UINT64_C(1)))),
                          Stmt::assign(UINT64_C(1),
                                       Expr::sub(Expr::var(UINT64_C(1)),
                                                 Expr::num(UINT64_C(1)))))),
                  Stmt::assign(UINT64_C(0), Expr::sub(Expr::var(UINT64_C(0)),
                                                      Expr::num(UINT64_C(1))))))));
}

std::pair<uint64_t, List<uint64_t>> ImpWhile::run_factorial(uint64_t k) {
  return run(STRefs::BUILD_STREFS, UINT64_C(2), factorial(k));
}

std::pair<uint64_t, List<uint64_t>> ImpWhile::run_fibonacci(uint64_t k) {
  return run(STRefs::BUILD_STREFS, UINT64_C(4), fibonacci(k));
}

std::pair<uint64_t, List<uint64_t>> ImpWhile::run_square(uint64_t k) {
  return run(STRefs::BUILD_STREFS, UINT64_C(3), square(k));
}

uint64_t ImpWhile::nth(uint64_t n, const List<uint64_t> &l, uint64_t default0) {
  if (n <= 0) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a0, _] = std::get<typename List<uint64_t>::Cons>(l.v());
      return a0;
    }
  } else {
    uint64_t m = n - 1;
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[_, a10] = std::get<typename List<uint64_t>::Cons>(l.v());
      return nth(m, *a10, default0);
    }
  }
}
