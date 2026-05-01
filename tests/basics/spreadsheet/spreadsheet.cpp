#include <spreadsheet.h>

bool Spreadsheet::cellref_eqb(const Spreadsheet::CellRef &r1,
                              const Spreadsheet::CellRef &r2) {
  return (r1.ref_col == r2.ref_col && r1.ref_row == r2.ref_row);
}

int64_t Spreadsheet::cell_index(const Spreadsheet::CellRef &r) {
  return ((((r.ref_row * NUM_COLS) & 0x7FFFFFFFFFFFFFFFLL) + r.ref_col) &
          0x7FFFFFFFFFFFFFFFLL);
}

Spreadsheet::Cell
Spreadsheet::get_cell(const persistent_array<Spreadsheet::Cell> s,
                      const Spreadsheet::CellRef &r) {
  return s.get(cell_index(r));
}

Spreadsheet::Sheet
Spreadsheet::set_cell(const persistent_array<Spreadsheet::Cell> s,
                      const Spreadsheet::CellRef &r,
                      const Spreadsheet::Cell &c) {
  return s.set(cell_index(r), c);
}

bool Spreadsheet::mem_cellref(const Spreadsheet::CellRef &r,
                              const List<Spreadsheet::CellRef> &xs) {
  if (std::holds_alternative<typename List<Spreadsheet::CellRef>::Nil>(
          xs.v())) {
    return false;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<Spreadsheet::CellRef>::Cons>(xs.v());
    if (cellref_eqb(r, d_a0)) {
      return true;
    } else {
      return mem_cellref(r, *(d_a1));
    }
  }
}

std::optional<int64_t> Spreadsheet::eval_expr(
    const unsigned int fuel, List<Spreadsheet::CellRef> visited,
    const persistent_array<Spreadsheet::Cell> s, const Spreadsheet::Expr &e) {
  if (fuel <= 0) {
    return std::optional<int64_t>();
  } else {
    unsigned int fuel_ = fuel - 1;
    if (std::holds_alternative<typename Spreadsheet::Expr::EInt>(e.v())) {
      const auto &[d_a0] = std::get<typename Spreadsheet::Expr::EInt>(e.v());
      return std::make_optional<int64_t>(d_a0);
    } else if (std::holds_alternative<typename Spreadsheet::Expr::ERef>(
                   e.v())) {
      const auto &[d_a0] = std::get<typename Spreadsheet::Expr::ERef>(e.v());
      if (mem_cellref(d_a0, visited)) {
        return std::optional<int64_t>();
      } else {
        auto &&_sv0 = get_cell(s, d_a0);
        if (std::holds_alternative<typename Spreadsheet::Cell::CEmpty>(
                _sv0.v())) {
          return std::make_optional<int64_t>(INT64_C(0));
        } else if (std::holds_alternative<typename Spreadsheet::Cell::CLit>(
                       _sv0.v())) {
          const auto &[d_a00] =
              std::get<typename Spreadsheet::Cell::CLit>(_sv0.v());
          return std::make_optional<int64_t>(d_a00);
        } else {
          const auto &[d_a00] =
              std::get<typename Spreadsheet::Cell::CForm>(_sv0.v());
          return eval_expr(
              fuel_, List<Spreadsheet::CellRef>::cons(d_a0, std::move(visited)),
              s, d_a00);
        }
      }
    } else if (std::holds_alternative<typename Spreadsheet::Expr::EAdd>(
                   e.v())) {
      const auto &[d_a0, d_a1] =
          std::get<typename Spreadsheet::Expr::EAdd>(e.v());
      auto _cs = eval_expr(fuel_, visited, s, *(d_a0));
      if (_cs.has_value()) {
        const int64_t &va = *_cs;
        auto _cs1 = eval_expr(fuel_, visited, s, *(d_a1));
        if (_cs1.has_value()) {
          const int64_t &vb = *_cs1;
          return std::make_optional<int64_t>((va + vb));
        } else {
          return std::optional<int64_t>();
        }
      } else {
        return std::optional<int64_t>();
      }
    } else if (std::holds_alternative<typename Spreadsheet::Expr::ESub>(
                   e.v())) {
      const auto &[d_a0, d_a1] =
          std::get<typename Spreadsheet::Expr::ESub>(e.v());
      auto _cs = eval_expr(fuel_, visited, s, *(d_a0));
      if (_cs.has_value()) {
        const int64_t &va = *_cs;
        auto _cs1 = eval_expr(fuel_, visited, s, *(d_a1));
        if (_cs1.has_value()) {
          const int64_t &vb = *_cs1;
          return std::make_optional<int64_t>((va - vb));
        } else {
          return std::optional<int64_t>();
        }
      } else {
        return std::optional<int64_t>();
      }
    } else if (std::holds_alternative<typename Spreadsheet::Expr::EMul>(
                   e.v())) {
      const auto &[d_a0, d_a1] =
          std::get<typename Spreadsheet::Expr::EMul>(e.v());
      auto _cs = eval_expr(fuel_, visited, s, *(d_a0));
      if (_cs.has_value()) {
        const int64_t &va = *_cs;
        auto _cs1 = eval_expr(fuel_, visited, s, *(d_a1));
        if (_cs1.has_value()) {
          const int64_t &vb = *_cs1;
          return std::make_optional<int64_t>((va * vb));
        } else {
          return std::optional<int64_t>();
        }
      } else {
        return std::optional<int64_t>();
      }
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename Spreadsheet::Expr::EDiv>(e.v());
      auto _cs = eval_expr(fuel_, visited, s, *(d_a0));
      if (_cs.has_value()) {
        const int64_t &va = *_cs;
        auto _cs1 = eval_expr(fuel_, visited, s, *(d_a1));
        if (_cs1.has_value()) {
          const int64_t &vb = *_cs1;
          if (vb == INT64_C(0)) {
            return std::optional<int64_t>();
          } else {
            return std::make_optional<int64_t>(
                (vb == 0 ? INT64_C(0) : va / vb));
          }
        } else {
          return std::optional<int64_t>();
        }
      } else {
        return std::optional<int64_t>();
      }
    }
  }
}

std::optional<int64_t>
Spreadsheet::eval_cell(const unsigned int fuel,
                       const persistent_array<Spreadsheet::Cell> s,
                       Spreadsheet::CellRef r) {
  auto &&_sv = get_cell(s, r);
  if (std::holds_alternative<typename Spreadsheet::Cell::CEmpty>(_sv.v())) {
    return std::make_optional<int64_t>(INT64_C(0));
  } else if (std::holds_alternative<typename Spreadsheet::Cell::CLit>(
                 _sv.v())) {
    const auto &[d_a0] = std::get<typename Spreadsheet::Cell::CLit>(_sv.v());
    return std::make_optional<int64_t>(d_a0);
  } else {
    const auto &[d_a0] = std::get<typename Spreadsheet::Cell::CForm>(_sv.v());
    return eval_expr(fuel,
                     List<Spreadsheet::CellRef>::cons(
                         std::move(r), List<Spreadsheet::CellRef>::nil()),
                     s, d_a0);
  }
}

unsigned int Nat::tail_add(const unsigned int n, const unsigned int m) {
  if (n <= 0) {
    return m;
  } else {
    unsigned int n0 = n - 1;
    return Nat::tail_add(n0, (m + 1));
  }
}

unsigned int Nat::tail_addmul(const unsigned int r, const unsigned int n,
                              const unsigned int m) {
  if (n <= 0) {
    return r;
  } else {
    unsigned int n0 = n - 1;
    return Nat::tail_addmul(Nat::tail_add(m, r), n0, m);
  }
}

unsigned int Nat::tail_mul(const unsigned int n, const unsigned int m) {
  return Nat::tail_addmul(0u, n, m);
}

unsigned int Nat::of_uint_acc(const Uint &d, const unsigned int acc) {
  if (std::holds_alternative<typename Uint::Nil>(d.v())) {
    return acc;
  } else if (std::holds_alternative<typename Uint::D0>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint::D0>(d.v());
    return Nat::of_uint_acc(*(d_a0), Nat::tail_mul(10u, acc));
  } else if (std::holds_alternative<typename Uint::D1>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint::D1>(d.v());
    return Nat::of_uint_acc(*(d_a0), (Nat::tail_mul(10u, acc) + 1));
  } else if (std::holds_alternative<typename Uint::D2>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint::D2>(d.v());
    return Nat::of_uint_acc(*(d_a0), ((Nat::tail_mul(10u, acc) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D3>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint::D3>(d.v());
    return Nat::of_uint_acc(*(d_a0), (((Nat::tail_mul(10u, acc) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D4>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint::D4>(d.v());
    return Nat::of_uint_acc(*(d_a0),
                            ((((Nat::tail_mul(10u, acc) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D5>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint::D5>(d.v());
    return Nat::of_uint_acc(
        *(d_a0), (((((Nat::tail_mul(10u, acc) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D6>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint::D6>(d.v());
    return Nat::of_uint_acc(
        *(d_a0), ((((((Nat::tail_mul(10u, acc) + 1) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D7>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint::D7>(d.v());
    return Nat::of_uint_acc(
        *(d_a0),
        (((((((Nat::tail_mul(10u, acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D8>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint::D8>(d.v());
    return Nat::of_uint_acc(
        *(d_a0),
        ((((((((Nat::tail_mul(10u, acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
         1));
  } else {
    const auto &[d_a0] = std::get<typename Uint::D9>(d.v());
    return Nat::of_uint_acc(
        *(d_a0),
        (((((((((Nat::tail_mul(10u, acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
          1) +
         1));
  }
}

unsigned int Nat::of_uint(const Uint &d) { return Nat::of_uint_acc(d, 0u); }

unsigned int Nat::of_hex_uint_acc(const Uint0 &d, const unsigned int acc) {
  if (std::holds_alternative<typename Uint0::Nil0>(d.v())) {
    return acc;
  } else if (std::holds_alternative<typename Uint0::D10>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::D10>(d.v());
    return Nat::of_hex_uint_acc(*(d_a0), Nat::tail_mul(16u, acc));
  } else if (std::holds_alternative<typename Uint0::D11>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::D11>(d.v());
    return Nat::of_hex_uint_acc(*(d_a0), (Nat::tail_mul(16u, acc) + 1));
  } else if (std::holds_alternative<typename Uint0::D12>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::D12>(d.v());
    return Nat::of_hex_uint_acc(*(d_a0), ((Nat::tail_mul(16u, acc) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D13>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::D13>(d.v());
    return Nat::of_hex_uint_acc(*(d_a0),
                                (((Nat::tail_mul(16u, acc) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D14>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::D14>(d.v());
    return Nat::of_hex_uint_acc(
        *(d_a0), ((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D15>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::D15>(d.v());
    return Nat::of_hex_uint_acc(
        *(d_a0), (((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D16>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::D16>(d.v());
    return Nat::of_hex_uint_acc(
        *(d_a0), ((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D17>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::D17>(d.v());
    return Nat::of_hex_uint_acc(
        *(d_a0),
        (((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D18>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::D18>(d.v());
    return Nat::of_hex_uint_acc(
        *(d_a0),
        ((((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
         1));
  } else if (std::holds_alternative<typename Uint0::D19>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::D19>(d.v());
    return Nat::of_hex_uint_acc(
        *(d_a0),
        (((((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::Da>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::Da>(d.v());
    return Nat::of_hex_uint_acc(
        *(d_a0),
        ((((((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::Db>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::Db>(d.v());
    return Nat::of_hex_uint_acc(
        *(d_a0),
        (((((((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
            1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::Dc>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::Dc>(d.v());
    return Nat::of_hex_uint_acc(
        *(d_a0),
        ((((((((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
             1) +
            1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::Dd>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::Dd>(d.v());
    return Nat::of_hex_uint_acc(
        *(d_a0),
        (((((((((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1) +
               1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::De>(d.v())) {
    const auto &[d_a0] = std::get<typename Uint0::De>(d.v());
    return Nat::of_hex_uint_acc(
        *(d_a0),
        ((((((((((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1));
  } else {
    const auto &[d_a0] = std::get<typename Uint0::Df>(d.v());
    return Nat::of_hex_uint_acc(
        *(d_a0),
        (((((((((((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1));
  }
}

unsigned int Nat::of_hex_uint(const Uint0 &d) {
  return Nat::of_hex_uint_acc(d, 0u);
}

unsigned int Nat::of_num_uint(const Uint1 &d) {
  if (std::holds_alternative<typename Uint1::UIntDecimal>(d.v())) {
    const auto &[d_u] = std::get<typename Uint1::UIntDecimal>(d.v());
    return Nat::of_uint(d_u);
  } else {
    const auto &[d_u] = std::get<typename Uint1::UIntHexadecimal>(d.v());
    return Nat::of_hex_uint(d_u);
  }
}
