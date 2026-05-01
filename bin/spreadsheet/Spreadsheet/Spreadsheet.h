#ifndef INCLUDED_SPREADSHEET
#define INCLUDED_SPREADSHEET

#include <cstdint>
#include <memory>
#include <optional>
#include <persistent_array.h>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct Spreadsheet {
  static inline const int64_t NUM_COLS = 104;
  static inline const int64_t NUM_ROWS = 100;
  static inline const int64_t GRID_SIZE =
      ((NUM_COLS * NUM_ROWS) & 0x7FFFFFFFFFFFFFFFLL);

  struct CellRef {
    int64_t ref_col;
    int64_t ref_row;

    // ACCESSORS
    CellRef clone() const {
      return CellRef{(*(this)).ref_col, (*(this)).ref_row};
    }
  };

  static int64_t cell_index(const CellRef &r);

  struct Expr {
    // TYPES
    struct EInt {
      int64_t d_a0;
    };

    struct ERef {
      CellRef d_a0;
    };

    struct EAdd {
      std::unique_ptr<Expr> d_a0;
      std::unique_ptr<Expr> d_a1;
    };

    struct ESub {
      std::unique_ptr<Expr> d_a0;
      std::unique_ptr<Expr> d_a1;
    };

    struct EMul {
      std::unique_ptr<Expr> d_a0;
      std::unique_ptr<Expr> d_a1;
    };

    struct EDiv {
      std::unique_ptr<Expr> d_a0;
      std::unique_ptr<Expr> d_a1;
    };

    using variant_t = std::variant<EInt, ERef, EAdd, ESub, EMul, EDiv>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    Expr() {}

    explicit Expr(EInt _v) : d_v_(std::move(_v)) {}

    explicit Expr(ERef _v) : d_v_(std::move(_v)) {}

    explicit Expr(EAdd _v) : d_v_(std::move(_v)) {}

    explicit Expr(ESub _v) : d_v_(std::move(_v)) {}

    explicit Expr(EMul _v) : d_v_(std::move(_v)) {}

    explicit Expr(EDiv _v) : d_v_(std::move(_v)) {}

    Expr(const Expr &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    Expr(Expr &&_other) : d_v_(std::move(_other.d_v_)) {}

    Expr &operator=(const Expr &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    Expr &operator=(Expr &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    Expr clone() const {
      Expr _out{};

      struct _CloneFrame {
        const Expr *_src;
        Expr *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const Expr *_src = _frame._src;
        Expr *_dst = _frame._dst;
        if (std::holds_alternative<EInt>(_src->v())) {
          const auto &_alt = std::get<EInt>(_src->v());
          _dst->d_v_ = EInt{_alt.d_a0};
        } else if (std::holds_alternative<ERef>(_src->v())) {
          const auto &_alt = std::get<ERef>(_src->v());
          _dst->d_v_ = ERef{_alt.d_a0.clone()};
        } else if (std::holds_alternative<EAdd>(_src->v())) {
          const auto &_alt = std::get<EAdd>(_src->v());
          _dst->d_v_ = EAdd{_alt.d_a0 ? std::make_unique<Expr>() : nullptr,
                            _alt.d_a1 ? std::make_unique<Expr>() : nullptr};
          auto &_dst_alt = std::get<EAdd>(_dst->d_v_);
          if (_alt.d_a0) {
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          }
          if (_alt.d_a1) {
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          }
        } else if (std::holds_alternative<ESub>(_src->v())) {
          const auto &_alt = std::get<ESub>(_src->v());
          _dst->d_v_ = ESub{_alt.d_a0 ? std::make_unique<Expr>() : nullptr,
                            _alt.d_a1 ? std::make_unique<Expr>() : nullptr};
          auto &_dst_alt = std::get<ESub>(_dst->d_v_);
          if (_alt.d_a0) {
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          }
          if (_alt.d_a1) {
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          }
        } else if (std::holds_alternative<EMul>(_src->v())) {
          const auto &_alt = std::get<EMul>(_src->v());
          _dst->d_v_ = EMul{_alt.d_a0 ? std::make_unique<Expr>() : nullptr,
                            _alt.d_a1 ? std::make_unique<Expr>() : nullptr};
          auto &_dst_alt = std::get<EMul>(_dst->d_v_);
          if (_alt.d_a0) {
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          }
          if (_alt.d_a1) {
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          }
        } else {
          const auto &_alt = std::get<EDiv>(_src->v());
          _dst->d_v_ = EDiv{_alt.d_a0 ? std::make_unique<Expr>() : nullptr,
                            _alt.d_a1 ? std::make_unique<Expr>() : nullptr};
          auto &_dst_alt = std::get<EDiv>(_dst->d_v_);
          if (_alt.d_a0) {
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          }
          if (_alt.d_a1) {
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static Expr eint(int64_t a0) { return Expr(EInt{std::move(a0)}); }

    static Expr eref(CellRef a0) { return Expr(ERef{std::move(a0)}); }

    static Expr eadd(Expr a0, Expr a1) {
      return Expr(EAdd{std::make_unique<Expr>(std::move(a0)),
                       std::make_unique<Expr>(std::move(a1))});
    }

    static Expr esub(Expr a0, Expr a1) {
      return Expr(ESub{std::make_unique<Expr>(std::move(a0)),
                       std::make_unique<Expr>(std::move(a1))});
    }

    static Expr emul(Expr a0, Expr a1) {
      return Expr(EMul{std::make_unique<Expr>(std::move(a0)),
                       std::make_unique<Expr>(std::move(a1))});
    }

    static Expr ediv(Expr a0, Expr a1) {
      return Expr(EDiv{std::make_unique<Expr>(std::move(a0)),
                       std::make_unique<Expr>(std::move(a1))});
    }

    // MANIPULATORS
    ~Expr() {
      std::vector<std::unique_ptr<Expr>> _stack{};
      auto _drain = [&](Expr &_node) {
        if (std::holds_alternative<EAdd>(_node.d_v_)) {
          auto &_alt = std::get<EAdd>(_node.d_v_);
          if (_alt.d_a0) {
            _stack.push_back(std::move(_alt.d_a0));
          }
          if (_alt.d_a1) {
            _stack.push_back(std::move(_alt.d_a1));
          }
        }
        if (std::holds_alternative<ESub>(_node.d_v_)) {
          auto &_alt = std::get<ESub>(_node.d_v_);
          if (_alt.d_a0) {
            _stack.push_back(std::move(_alt.d_a0));
          }
          if (_alt.d_a1) {
            _stack.push_back(std::move(_alt.d_a1));
          }
        }
        if (std::holds_alternative<EMul>(_node.d_v_)) {
          auto &_alt = std::get<EMul>(_node.d_v_);
          if (_alt.d_a0) {
            _stack.push_back(std::move(_alt.d_a0));
          }
          if (_alt.d_a1) {
            _stack.push_back(std::move(_alt.d_a1));
          }
        }
        if (std::holds_alternative<EDiv>(_node.d_v_)) {
          auto &_alt = std::get<EDiv>(_node.d_v_);
          if (_alt.d_a0) {
            _stack.push_back(std::move(_alt.d_a0));
          }
          if (_alt.d_a1) {
            _stack.push_back(std::move(_alt.d_a1));
          }
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node) {
          _drain(*_node);
        }
      }
    }

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }

    template <
        typename T1, MapsTo<T1, int64_t> F0, MapsTo<T1, CellRef> F1,
        MapsTo<T1, Expr, T1, Expr, T1> F2, MapsTo<T1, Expr, T1, Expr, T1> F3,
        MapsTo<T1, Expr, T1, Expr, T1> F4, MapsTo<T1, Expr, T1, Expr, T1> F5>
    T1 Expr_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename Expr::EInt>(_sv.v())) {
        const auto &[d_a0] = std::get<typename Expr::EInt>(_sv.v());
        return f(d_a0);
      } else if (std::holds_alternative<typename Expr::ERef>(_sv.v())) {
        const auto &[d_a0] = std::get<typename Expr::ERef>(_sv.v());
        return f0(d_a0);
      } else if (std::holds_alternative<typename Expr::EAdd>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename Expr::EAdd>(_sv.v());
        return f1(
            *(d_a0), (*(d_a0)).template Expr_rec<T1>(f, f0, f1, f2, f3, f4),
            *(d_a1), (*(d_a1)).template Expr_rec<T1>(f, f0, f1, f2, f3, f4));
      } else if (std::holds_alternative<typename Expr::ESub>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename Expr::ESub>(_sv.v());
        return f2(
            *(d_a0), (*(d_a0)).template Expr_rec<T1>(f, f0, f1, f2, f3, f4),
            *(d_a1), (*(d_a1)).template Expr_rec<T1>(f, f0, f1, f2, f3, f4));
      } else if (std::holds_alternative<typename Expr::EMul>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename Expr::EMul>(_sv.v());
        return f3(
            *(d_a0), (*(d_a0)).template Expr_rec<T1>(f, f0, f1, f2, f3, f4),
            *(d_a1), (*(d_a1)).template Expr_rec<T1>(f, f0, f1, f2, f3, f4));
      } else {
        const auto &[d_a0, d_a1] = std::get<typename Expr::EDiv>(_sv.v());
        return f4(
            *(d_a0), (*(d_a0)).template Expr_rec<T1>(f, f0, f1, f2, f3, f4),
            *(d_a1), (*(d_a1)).template Expr_rec<T1>(f, f0, f1, f2, f3, f4));
      }
    }

    template <
        typename T1, MapsTo<T1, int64_t> F0, MapsTo<T1, CellRef> F1,
        MapsTo<T1, Expr, T1, Expr, T1> F2, MapsTo<T1, Expr, T1, Expr, T1> F3,
        MapsTo<T1, Expr, T1, Expr, T1> F4, MapsTo<T1, Expr, T1, Expr, T1> F5>
    T1 Expr_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename Expr::EInt>(_sv.v())) {
        const auto &[d_a0] = std::get<typename Expr::EInt>(_sv.v());
        return f(d_a0);
      } else if (std::holds_alternative<typename Expr::ERef>(_sv.v())) {
        const auto &[d_a0] = std::get<typename Expr::ERef>(_sv.v());
        return f0(d_a0);
      } else if (std::holds_alternative<typename Expr::EAdd>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename Expr::EAdd>(_sv.v());
        return f1(
            *(d_a0), (*(d_a0)).template Expr_rect<T1>(f, f0, f1, f2, f3, f4),
            *(d_a1), (*(d_a1)).template Expr_rect<T1>(f, f0, f1, f2, f3, f4));
      } else if (std::holds_alternative<typename Expr::ESub>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename Expr::ESub>(_sv.v());
        return f2(
            *(d_a0), (*(d_a0)).template Expr_rect<T1>(f, f0, f1, f2, f3, f4),
            *(d_a1), (*(d_a1)).template Expr_rect<T1>(f, f0, f1, f2, f3, f4));
      } else if (std::holds_alternative<typename Expr::EMul>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename Expr::EMul>(_sv.v());
        return f3(
            *(d_a0), (*(d_a0)).template Expr_rect<T1>(f, f0, f1, f2, f3, f4),
            *(d_a1), (*(d_a1)).template Expr_rect<T1>(f, f0, f1, f2, f3, f4));
      } else {
        const auto &[d_a0, d_a1] = std::get<typename Expr::EDiv>(_sv.v());
        return f4(
            *(d_a0), (*(d_a0)).template Expr_rect<T1>(f, f0, f1, f2, f3, f4),
            *(d_a1), (*(d_a1)).template Expr_rect<T1>(f, f0, f1, f2, f3, f4));
      }
    }
  };

  struct Cell {
    // TYPES
    struct CEmpty {};

    struct CLit {
      int64_t d_a0;
    };

    struct CForm {
      Expr d_a0;
    };

    using variant_t = std::variant<CEmpty, CLit, CForm>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    Cell() {}

    explicit Cell(CEmpty _v) : d_v_(_v) {}

    explicit Cell(CLit _v) : d_v_(std::move(_v)) {}

    explicit Cell(CForm _v) : d_v_(std::move(_v)) {}

    Cell(const Cell &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    Cell(Cell &&_other) : d_v_(std::move(_other.d_v_)) {}

    Cell &operator=(const Cell &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    Cell &operator=(Cell &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    Cell clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<CEmpty>(_sv.v())) {
        return Cell(CEmpty{});
      } else if (std::holds_alternative<CLit>(_sv.v())) {
        const auto &[d_a0] = std::get<CLit>(_sv.v());
        return Cell(CLit{d_a0});
      } else {
        const auto &[d_a0] = std::get<CForm>(_sv.v());
        return Cell(CForm{d_a0.clone()});
      }
    }

    // CREATORS
    static Cell cempty() { return Cell(CEmpty{}); }

    static Cell clit(int64_t a0) { return Cell(CLit{std::move(a0)}); }

    static Cell cform(Expr a0) { return Cell(CForm{std::move(a0)}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, int64_t> F1, MapsTo<T1, Expr> F2>
  static T1 Cell_rect(const T1 f, F1 &&f0, F2 &&f1, const Cell &c) {
    if (std::holds_alternative<typename Cell::CEmpty>(c.v())) {
      return f;
    } else if (std::holds_alternative<typename Cell::CLit>(c.v())) {
      const auto &[d_a0] = std::get<typename Cell::CLit>(c.v());
      return f0(d_a0);
    } else {
      const auto &[d_a0] = std::get<typename Cell::CForm>(c.v());
      return f1(d_a0);
    }
  }

  template <typename T1, MapsTo<T1, int64_t> F1, MapsTo<T1, Expr> F2>
  static T1 Cell_rec(const T1 f, F1 &&f0, F2 &&f1, const Cell &c) {
    if (std::holds_alternative<typename Cell::CEmpty>(c.v())) {
      return f;
    } else if (std::holds_alternative<typename Cell::CLit>(c.v())) {
      const auto &[d_a0] = std::get<typename Cell::CLit>(c.v());
      return f0(d_a0);
    } else {
      const auto &[d_a0] = std::get<typename Cell::CForm>(c.v());
      return f1(d_a0);
    }
  }

  using Sheet = persistent_array<Cell>;
  static inline const Sheet new_sheet =
      persistent_array<Cell>(GRID_SIZE, Cell::cempty());
  static Cell get_cell(const persistent_array<Cell> s, const CellRef &r);
  static Sheet set_cell(const persistent_array<Cell> s, const CellRef &r,
                        const Cell &c);
  static std::optional<int64_t> eval_expr(const unsigned int fuel,
                                          const persistent_array<Cell> s,
                                          const Expr &e);
  static std::optional<int64_t> eval_cell(const unsigned int fuel,
                                          const persistent_array<Cell> s,
                                          const CellRef &r);
  static inline const unsigned int DEFAULT_FUEL = 1000u;
  static inline const std::optional<int64_t> smoke = []() {
    CellRef a1 = CellRef{0, 0};
    CellRef b1 = CellRef{1, 0};
    CellRef c1 = CellRef{2, 0};
    persistent_array<Cell> s1 = set_cell(new_sheet, a1, Cell::clit(INT64_C(2)));
    persistent_array<Cell> s2 = set_cell(s1, b1, Cell::clit(INT64_C(3)));
    persistent_array<Cell> s3 =
        set_cell(s2, c1,
                 Cell::cform(Expr::emul(Expr::eadd(Expr::eref(std::move(a1)),
                                                   Expr::eref(std::move(b1))),
                                        Expr::eint(INT64_C(7)))));
    return eval_cell(DEFAULT_FUEL, s3, std::move(c1));
  }();
};

#endif // INCLUDED_SPREADSHEET
