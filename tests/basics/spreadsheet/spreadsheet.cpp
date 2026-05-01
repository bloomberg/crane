#include <spreadsheet.h>

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

std::optional<int64_t>
Spreadsheet::eval_expr(const unsigned int fuel,
                       const persistent_array<Spreadsheet::Cell> s,
                       const Spreadsheet::Expr &e) {
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
        return eval_expr(fuel_, s, d_a00);
      }
    } else if (std::holds_alternative<typename Spreadsheet::Expr::EAdd>(
                   e.v())) {
      const auto &[d_a0, d_a1] =
          std::get<typename Spreadsheet::Expr::EAdd>(e.v());
      auto _cs = eval_expr(fuel_, s, *(d_a0));
      if (_cs.has_value()) {
        const int64_t &va = *_cs;
        auto _cs1 = eval_expr(fuel_, s, *(d_a1));
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
      auto _cs = eval_expr(fuel_, s, *(d_a0));
      if (_cs.has_value()) {
        const int64_t &va = *_cs;
        auto _cs1 = eval_expr(fuel_, s, *(d_a1));
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
      auto _cs = eval_expr(fuel_, s, *(d_a0));
      if (_cs.has_value()) {
        const int64_t &va = *_cs;
        auto _cs1 = eval_expr(fuel_, s, *(d_a1));
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
      auto _cs = eval_expr(fuel_, s, *(d_a0));
      if (_cs.has_value()) {
        const int64_t &va = *_cs;
        auto _cs1 = eval_expr(fuel_, s, *(d_a1));
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
                       const Spreadsheet::CellRef &r) {
  auto &&_sv = get_cell(s, r);
  if (std::holds_alternative<typename Spreadsheet::Cell::CEmpty>(_sv.v())) {
    return std::make_optional<int64_t>(INT64_C(0));
  } else if (std::holds_alternative<typename Spreadsheet::Cell::CLit>(
                 _sv.v())) {
    const auto &[d_a0] = std::get<typename Spreadsheet::Cell::CLit>(_sv.v());
    return std::make_optional<int64_t>(d_a0);
  } else {
    const auto &[d_a0] = std::get<typename Spreadsheet::Cell::CForm>(_sv.v());
    return eval_expr(fuel, s, d_a0);
  }
}
