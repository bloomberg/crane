#ifndef INCLUDED_LARGE_MUTUAL
#define INCLUDED_LARGE_MUTUAL

#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct LargeMutual {
  struct stmt;
  struct expr;
  struct bexpr;

  struct stmt {
    // TYPES
    struct SAssign {
      uint64_t a0;
      std::shared_ptr<expr> a1;
    };

    struct SSeq {
      std::shared_ptr<stmt> a0;
      std::shared_ptr<stmt> a1;
    };

    struct SIf {
      std::shared_ptr<bexpr> a0;
      std::shared_ptr<stmt> a1;
      std::shared_ptr<stmt> a2;
    };

    struct SWhile {
      std::shared_ptr<bexpr> a0;
      std::shared_ptr<stmt> a1;
    };

    struct SSkip {};

    using variant_t = std::variant<SAssign, SSeq, SIf, SWhile, SSkip>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    stmt() {}

    explicit stmt(SAssign _v) : v_(std::move(_v)) {}

    explicit stmt(SSeq _v) : v_(std::move(_v)) {}

    explicit stmt(SIf _v) : v_(std::move(_v)) {}

    explicit stmt(SWhile _v) : v_(std::move(_v)) {}

    explicit stmt(SSkip _v) : v_(_v) {}

    static stmt sassign(uint64_t a0, expr a1) {
      return stmt(SAssign{a0, std::make_shared<expr>(std::move(a1))});
    }

    static stmt sseq(stmt a0, stmt a1) {
      return stmt(SSeq{std::make_shared<stmt>(std::move(a0)),
                       std::make_shared<stmt>(std::move(a1))});
    }

    static stmt sif(bexpr a0, stmt a1, stmt a2) {
      return stmt(SIf{std::make_shared<bexpr>(std::move(a0)),
                      std::make_shared<stmt>(std::move(a1)),
                      std::make_shared<stmt>(std::move(a2))});
    }

    static stmt swhile(bexpr a0, stmt a1) {
      return stmt(SWhile{std::make_shared<bexpr>(std::move(a0)),
                         std::make_shared<stmt>(std::move(a1))});
    }

    static stmt sskip() { return stmt(SSkip{}); }

    // MANIPULATORS
    ~stmt() {
      std::vector<std::any> _stack = {};
      auto _drain_self = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<SAssign>(&_v)) {
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
        if (auto *_alt = std::get_if<SSeq>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
        if (auto *_alt = std::get_if<SIf>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
          if (_alt->a2) {
            _stack.push_back(std::move(_alt->a2));
          }
        }
        if (auto *_alt = std::get_if<SWhile>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
      };
      _drain_self(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (auto *_sp = std::any_cast<std::shared_ptr<stmt>>(&_cur)) {
          if (*_sp && (*_sp).use_count() == 1) {
            _drain_self((*_sp)->v_mut());
          }
        } else {
          if (auto *_sp = std::any_cast<std::shared_ptr<expr>>(&_cur)) {
            if (*_sp && (*_sp).use_count() == 1) {
              auto &_pv = (*_sp)->v_mut();
              if (auto *_alt = std::get_if<typename expr::EAdd>(&_pv)) {
                if (_alt->a0) {
                  _stack.push_back(std::move(_alt->a0));
                }
                if (_alt->a1) {
                  _stack.push_back(std::move(_alt->a1));
                }
              }
              if (auto *_alt = std::get_if<typename expr::EMul>(&_pv)) {
                if (_alt->a0) {
                  _stack.push_back(std::move(_alt->a0));
                }
                if (_alt->a1) {
                  _stack.push_back(std::move(_alt->a1));
                }
              }
              if (auto *_alt = std::get_if<typename expr::ECond>(&_pv)) {
                if (_alt->a0) {
                  _stack.push_back(std::move(_alt->a0));
                }
                if (_alt->a1) {
                  _stack.push_back(std::move(_alt->a1));
                }
                if (_alt->a2) {
                  _stack.push_back(std::move(_alt->a2));
                }
              }
            }
          } else {
            if (auto *_sp = std::any_cast<std::shared_ptr<bexpr>>(&_cur)) {
              if (*_sp && (*_sp).use_count() == 1) {
                auto &_pv = (*_sp)->v_mut();
                if (auto *_alt = std::get_if<typename bexpr::BEq>(&_pv)) {
                  if (_alt->a0) {
                    _stack.push_back(std::move(_alt->a0));
                  }
                  if (_alt->a1) {
                    _stack.push_back(std::move(_alt->a1));
                  }
                }
                if (auto *_alt = std::get_if<typename bexpr::BLt>(&_pv)) {
                  if (_alt->a0) {
                    _stack.push_back(std::move(_alt->a0));
                  }
                  if (_alt->a1) {
                    _stack.push_back(std::move(_alt->a1));
                  }
                }
                if (auto *_alt = std::get_if<typename bexpr::BAnd>(&_pv)) {
                  if (_alt->a0) {
                    _stack.push_back(std::move(_alt->a0));
                  }
                  if (_alt->a1) {
                    _stack.push_back(std::move(_alt->a1));
                  }
                }
                if (auto *_alt = std::get_if<typename bexpr::BOr>(&_pv)) {
                  if (_alt->a0) {
                    _stack.push_back(std::move(_alt->a0));
                  }
                  if (_alt->a1) {
                    _stack.push_back(std::move(_alt->a1));
                  }
                }
                if (auto *_alt = std::get_if<typename bexpr::BNot>(&_pv)) {
                  if (_alt->a0) {
                    _stack.push_back(std::move(_alt->a0));
                  }
                }
              }
            }
          }
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  struct expr {
    // TYPES
    struct ENum {
      uint64_t a0;
    };

    struct EVar {
      uint64_t a0;
    };

    struct EAdd {
      std::shared_ptr<expr> a0;
      std::shared_ptr<expr> a1;
    };

    struct EMul {
      std::shared_ptr<expr> a0;
      std::shared_ptr<expr> a1;
    };

    struct ECond {
      std::shared_ptr<bexpr> a0;
      std::shared_ptr<expr> a1;
      std::shared_ptr<expr> a2;
    };

    using variant_t = std::variant<ENum, EVar, EAdd, EMul, ECond>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    expr() {}

    explicit expr(ENum _v) : v_(std::move(_v)) {}

    explicit expr(EVar _v) : v_(std::move(_v)) {}

    explicit expr(EAdd _v) : v_(std::move(_v)) {}

    explicit expr(EMul _v) : v_(std::move(_v)) {}

    explicit expr(ECond _v) : v_(std::move(_v)) {}

    static expr ENum_(uint64_t a0) { return expr(ENum{a0}); }

    static expr evar(uint64_t a0) { return expr(EVar{a0}); }

    static expr eadd(expr a0, expr a1) {
      return expr(EAdd{std::make_shared<expr>(std::move(a0)),
                       std::make_shared<expr>(std::move(a1))});
    }

    static expr emul(expr a0, expr a1) {
      return expr(EMul{std::make_shared<expr>(std::move(a0)),
                       std::make_shared<expr>(std::move(a1))});
    }

    static expr econd(bexpr a0, expr a1, expr a2) {
      return expr(ECond{std::make_shared<bexpr>(std::move(a0)),
                        std::make_shared<expr>(std::move(a1)),
                        std::make_shared<expr>(std::move(a2))});
    }

    // MANIPULATORS
    ~expr() {
      std::vector<std::any> _stack = {};
      auto _drain_self = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<EAdd>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
        if (auto *_alt = std::get_if<EMul>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
        if (auto *_alt = std::get_if<ECond>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
          if (_alt->a2) {
            _stack.push_back(std::move(_alt->a2));
          }
        }
      };
      _drain_self(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (auto *_sp = std::any_cast<std::shared_ptr<expr>>(&_cur)) {
          if (*_sp && (*_sp).use_count() == 1) {
            _drain_self((*_sp)->v_mut());
          }
        } else {
          if (auto *_sp = std::any_cast<std::shared_ptr<stmt>>(&_cur)) {
            if (*_sp && (*_sp).use_count() == 1) {
              auto &_pv = (*_sp)->v_mut();
              if (auto *_alt = std::get_if<typename stmt::SAssign>(&_pv)) {
                if (_alt->a1) {
                  _stack.push_back(std::move(_alt->a1));
                }
              }
              if (auto *_alt = std::get_if<typename stmt::SSeq>(&_pv)) {
                if (_alt->a0) {
                  _stack.push_back(std::move(_alt->a0));
                }
                if (_alt->a1) {
                  _stack.push_back(std::move(_alt->a1));
                }
              }
              if (auto *_alt = std::get_if<typename stmt::SIf>(&_pv)) {
                if (_alt->a0) {
                  _stack.push_back(std::move(_alt->a0));
                }
                if (_alt->a1) {
                  _stack.push_back(std::move(_alt->a1));
                }
                if (_alt->a2) {
                  _stack.push_back(std::move(_alt->a2));
                }
              }
              if (auto *_alt = std::get_if<typename stmt::SWhile>(&_pv)) {
                if (_alt->a0) {
                  _stack.push_back(std::move(_alt->a0));
                }
                if (_alt->a1) {
                  _stack.push_back(std::move(_alt->a1));
                }
              }
            }
          } else {
            if (auto *_sp = std::any_cast<std::shared_ptr<bexpr>>(&_cur)) {
              if (*_sp && (*_sp).use_count() == 1) {
                auto &_pv = (*_sp)->v_mut();
                if (auto *_alt = std::get_if<typename bexpr::BEq>(&_pv)) {
                  if (_alt->a0) {
                    _stack.push_back(std::move(_alt->a0));
                  }
                  if (_alt->a1) {
                    _stack.push_back(std::move(_alt->a1));
                  }
                }
                if (auto *_alt = std::get_if<typename bexpr::BLt>(&_pv)) {
                  if (_alt->a0) {
                    _stack.push_back(std::move(_alt->a0));
                  }
                  if (_alt->a1) {
                    _stack.push_back(std::move(_alt->a1));
                  }
                }
                if (auto *_alt = std::get_if<typename bexpr::BAnd>(&_pv)) {
                  if (_alt->a0) {
                    _stack.push_back(std::move(_alt->a0));
                  }
                  if (_alt->a1) {
                    _stack.push_back(std::move(_alt->a1));
                  }
                }
                if (auto *_alt = std::get_if<typename bexpr::BOr>(&_pv)) {
                  if (_alt->a0) {
                    _stack.push_back(std::move(_alt->a0));
                  }
                  if (_alt->a1) {
                    _stack.push_back(std::move(_alt->a1));
                  }
                }
                if (auto *_alt = std::get_if<typename bexpr::BNot>(&_pv)) {
                  if (_alt->a0) {
                    _stack.push_back(std::move(_alt->a0));
                  }
                }
              }
            }
          }
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  struct bexpr {
    // TYPES
    struct BTrue {};

    struct BFalse {};

    struct BEq {
      std::shared_ptr<expr> a0;
      std::shared_ptr<expr> a1;
    };

    struct BLt {
      std::shared_ptr<expr> a0;
      std::shared_ptr<expr> a1;
    };

    struct BAnd {
      std::shared_ptr<bexpr> a0;
      std::shared_ptr<bexpr> a1;
    };

    struct BOr {
      std::shared_ptr<bexpr> a0;
      std::shared_ptr<bexpr> a1;
    };

    struct BNot {
      std::shared_ptr<bexpr> a0;
    };

    using variant_t = std::variant<BTrue, BFalse, BEq, BLt, BAnd, BOr, BNot>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    bexpr() {}

    explicit bexpr(BTrue _v) : v_(_v) {}

    explicit bexpr(BFalse _v) : v_(_v) {}

    explicit bexpr(BEq _v) : v_(std::move(_v)) {}

    explicit bexpr(BLt _v) : v_(std::move(_v)) {}

    explicit bexpr(BAnd _v) : v_(std::move(_v)) {}

    explicit bexpr(BOr _v) : v_(std::move(_v)) {}

    explicit bexpr(BNot _v) : v_(std::move(_v)) {}

    static bexpr btrue() { return bexpr(BTrue{}); }

    static bexpr bfalse() { return bexpr(BFalse{}); }

    static bexpr beq(expr a0, expr a1) {
      return bexpr(BEq{std::make_shared<expr>(std::move(a0)),
                       std::make_shared<expr>(std::move(a1))});
    }

    static bexpr blt(expr a0, expr a1) {
      return bexpr(BLt{std::make_shared<expr>(std::move(a0)),
                       std::make_shared<expr>(std::move(a1))});
    }

    static bexpr band(bexpr a0, bexpr a1) {
      return bexpr(BAnd{std::make_shared<bexpr>(std::move(a0)),
                        std::make_shared<bexpr>(std::move(a1))});
    }

    static bexpr bor(bexpr a0, bexpr a1) {
      return bexpr(BOr{std::make_shared<bexpr>(std::move(a0)),
                       std::make_shared<bexpr>(std::move(a1))});
    }

    static bexpr bnot(bexpr a0) {
      return bexpr(BNot{std::make_shared<bexpr>(std::move(a0))});
    }

    // MANIPULATORS
    ~bexpr() {
      std::vector<std::any> _stack = {};
      auto _drain_self = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<BEq>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
        if (auto *_alt = std::get_if<BLt>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
        if (auto *_alt = std::get_if<BAnd>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
        if (auto *_alt = std::get_if<BOr>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
        if (auto *_alt = std::get_if<BNot>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
        }
      };
      _drain_self(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (auto *_sp = std::any_cast<std::shared_ptr<bexpr>>(&_cur)) {
          if (*_sp && (*_sp).use_count() == 1) {
            _drain_self((*_sp)->v_mut());
          }
        } else {
          if (auto *_sp = std::any_cast<std::shared_ptr<stmt>>(&_cur)) {
            if (*_sp && (*_sp).use_count() == 1) {
              auto &_pv = (*_sp)->v_mut();
              if (auto *_alt = std::get_if<typename stmt::SAssign>(&_pv)) {
                if (_alt->a1) {
                  _stack.push_back(std::move(_alt->a1));
                }
              }
              if (auto *_alt = std::get_if<typename stmt::SSeq>(&_pv)) {
                if (_alt->a0) {
                  _stack.push_back(std::move(_alt->a0));
                }
                if (_alt->a1) {
                  _stack.push_back(std::move(_alt->a1));
                }
              }
              if (auto *_alt = std::get_if<typename stmt::SIf>(&_pv)) {
                if (_alt->a0) {
                  _stack.push_back(std::move(_alt->a0));
                }
                if (_alt->a1) {
                  _stack.push_back(std::move(_alt->a1));
                }
                if (_alt->a2) {
                  _stack.push_back(std::move(_alt->a2));
                }
              }
              if (auto *_alt = std::get_if<typename stmt::SWhile>(&_pv)) {
                if (_alt->a0) {
                  _stack.push_back(std::move(_alt->a0));
                }
                if (_alt->a1) {
                  _stack.push_back(std::move(_alt->a1));
                }
              }
            }
          } else {
            if (auto *_sp = std::any_cast<std::shared_ptr<expr>>(&_cur)) {
              if (*_sp && (*_sp).use_count() == 1) {
                auto &_pv = (*_sp)->v_mut();
                if (auto *_alt = std::get_if<typename expr::EAdd>(&_pv)) {
                  if (_alt->a0) {
                    _stack.push_back(std::move(_alt->a0));
                  }
                  if (_alt->a1) {
                    _stack.push_back(std::move(_alt->a1));
                  }
                }
                if (auto *_alt = std::get_if<typename expr::EMul>(&_pv)) {
                  if (_alt->a0) {
                    _stack.push_back(std::move(_alt->a0));
                  }
                  if (_alt->a1) {
                    _stack.push_back(std::move(_alt->a1));
                  }
                }
                if (auto *_alt = std::get_if<typename expr::ECond>(&_pv)) {
                  if (_alt->a0) {
                    _stack.push_back(std::move(_alt->a0));
                  }
                  if (_alt->a1) {
                    _stack.push_back(std::move(_alt->a1));
                  }
                  if (_alt->a2) {
                    _stack.push_back(std::move(_alt->a2));
                  }
                }
              }
            }
          }
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1, typename F2, typename F3>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, expr &> &&
             std::is_invocable_r_v<T1, F1 &, stmt &, T1 &, stmt &, T1 &> &&
             std::is_invocable_r_v<T1, F2 &, bexpr &, stmt &, T1 &, stmt &,
                                   T1 &> &&
             std::is_invocable_r_v<T1, F3 &, bexpr &, stmt &, T1 &>
  static T1 stmt_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, T1 f3, const stmt &s) {
    if (std::holds_alternative<typename stmt::SAssign>(s.v())) {
      const auto &[a0, a1] = std::get<typename stmt::SAssign>(s.v());
      return f(a0, *a1);
    } else if (std::holds_alternative<typename stmt::SSeq>(s.v())) {
      const auto &[a0, a1] = std::get<typename stmt::SSeq>(s.v());
      return f0(*a0, stmt_rect<T1>(f, f0, f1, f2, f3, *a0), *a1,
                stmt_rect<T1>(f, f0, f1, f2, f3, *a1));
    } else if (std::holds_alternative<typename stmt::SIf>(s.v())) {
      const auto &[a0, a1, a2] = std::get<typename stmt::SIf>(s.v());
      return f1(*a0, *a1, stmt_rect<T1>(f, f0, f1, f2, f3, *a1), *a2,
                stmt_rect<T1>(f, f0, f1, f2, f3, *a2));
    } else if (std::holds_alternative<typename stmt::SWhile>(s.v())) {
      const auto &[a0, a1] = std::get<typename stmt::SWhile>(s.v());
      return f2(*a0, *a1, stmt_rect<T1>(f, f0, f1, f2, f3, *a1));
    } else {
      return f3;
    }
  }

  template <typename T1, typename F0, typename F1, typename F2, typename F3>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, expr &> &&
             std::is_invocable_r_v<T1, F1 &, stmt &, T1 &, stmt &, T1 &> &&
             std::is_invocable_r_v<T1, F2 &, bexpr &, stmt &, T1 &, stmt &,
                                   T1 &> &&
             std::is_invocable_r_v<T1, F3 &, bexpr &, stmt &, T1 &>
  static T1 stmt_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, T1 f3, const stmt &s) {
    if (std::holds_alternative<typename stmt::SAssign>(s.v())) {
      const auto &[a0, a1] = std::get<typename stmt::SAssign>(s.v());
      return f(a0, *a1);
    } else if (std::holds_alternative<typename stmt::SSeq>(s.v())) {
      const auto &[a0, a1] = std::get<typename stmt::SSeq>(s.v());
      return f0(*a0, stmt_rec<T1>(f, f0, f1, f2, f3, *a0), *a1,
                stmt_rec<T1>(f, f0, f1, f2, f3, *a1));
    } else if (std::holds_alternative<typename stmt::SIf>(s.v())) {
      const auto &[a0, a1, a2] = std::get<typename stmt::SIf>(s.v());
      return f1(*a0, *a1, stmt_rec<T1>(f, f0, f1, f2, f3, *a1), *a2,
                stmt_rec<T1>(f, f0, f1, f2, f3, *a2));
    } else if (std::holds_alternative<typename stmt::SWhile>(s.v())) {
      const auto &[a0, a1] = std::get<typename stmt::SWhile>(s.v());
      return f2(*a0, *a1, stmt_rec<T1>(f, f0, f1, f2, f3, *a1));
    } else {
      return f3;
    }
  }

  template <typename T1, typename F0, typename F1, typename F2, typename F3,
            typename F4>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F2 &, expr &, T1 &, expr &, T1 &> &&
             std::is_invocable_r_v<T1, F3 &, expr &, T1 &, expr &, T1 &> &&
             std::is_invocable_r_v<T1, F4 &, bexpr &, expr &, T1 &, expr &,
                                   T1 &>
  static T1 expr_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3,
                      const expr &e) {
    if (std::holds_alternative<typename expr::ENum>(e.v())) {
      const auto &[a0] = std::get<typename expr::ENum>(e.v());
      return f(a0);
    } else if (std::holds_alternative<typename expr::EVar>(e.v())) {
      const auto &[a0] = std::get<typename expr::EVar>(e.v());
      return f0(a0);
    } else if (std::holds_alternative<typename expr::EAdd>(e.v())) {
      const auto &[a0, a1] = std::get<typename expr::EAdd>(e.v());
      return f1(*a0, expr_rect<T1>(f, f0, f1, f2, f3, *a0), *a1,
                expr_rect<T1>(f, f0, f1, f2, f3, *a1));
    } else if (std::holds_alternative<typename expr::EMul>(e.v())) {
      const auto &[a0, a1] = std::get<typename expr::EMul>(e.v());
      return f2(*a0, expr_rect<T1>(f, f0, f1, f2, f3, *a0), *a1,
                expr_rect<T1>(f, f0, f1, f2, f3, *a1));
    } else {
      const auto &[a0, a1, a2] = std::get<typename expr::ECond>(e.v());
      return f3(*a0, *a1, expr_rect<T1>(f, f0, f1, f2, f3, *a1), *a2,
                expr_rect<T1>(f, f0, f1, f2, f3, *a2));
    }
  }

  template <typename T1, typename F0, typename F1, typename F2, typename F3,
            typename F4>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F2 &, expr &, T1 &, expr &, T1 &> &&
             std::is_invocable_r_v<T1, F3 &, expr &, T1 &, expr &, T1 &> &&
             std::is_invocable_r_v<T1, F4 &, bexpr &, expr &, T1 &, expr &,
                                   T1 &>
  static T1 expr_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3,
                     const expr &e) {
    if (std::holds_alternative<typename expr::ENum>(e.v())) {
      const auto &[a0] = std::get<typename expr::ENum>(e.v());
      return f(a0);
    } else if (std::holds_alternative<typename expr::EVar>(e.v())) {
      const auto &[a0] = std::get<typename expr::EVar>(e.v());
      return f0(a0);
    } else if (std::holds_alternative<typename expr::EAdd>(e.v())) {
      const auto &[a0, a1] = std::get<typename expr::EAdd>(e.v());
      return f1(*a0, expr_rec<T1>(f, f0, f1, f2, f3, *a0), *a1,
                expr_rec<T1>(f, f0, f1, f2, f3, *a1));
    } else if (std::holds_alternative<typename expr::EMul>(e.v())) {
      const auto &[a0, a1] = std::get<typename expr::EMul>(e.v());
      return f2(*a0, expr_rec<T1>(f, f0, f1, f2, f3, *a0), *a1,
                expr_rec<T1>(f, f0, f1, f2, f3, *a1));
    } else {
      const auto &[a0, a1, a2] = std::get<typename expr::ECond>(e.v());
      return f3(*a0, *a1, expr_rec<T1>(f, f0, f1, f2, f3, *a1), *a2,
                expr_rec<T1>(f, f0, f1, f2, f3, *a2));
    }
  }

  template <typename T1, typename F2, typename F3, typename F4, typename F5,
            typename F6>
    requires std::is_invocable_r_v<T1, F2 &, expr &, expr &> &&
             std::is_invocable_r_v<T1, F3 &, expr &, expr &> &&
             std::is_invocable_r_v<T1, F4 &, bexpr &, T1 &, bexpr &, T1 &> &&
             std::is_invocable_r_v<T1, F5 &, bexpr &, T1 &, bexpr &, T1 &> &&
             std::is_invocable_r_v<T1, F6 &, bexpr &, T1 &>
  static T1 bexpr_rect(T1 f, T1 f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4, F6 &&f5,
                       const bexpr &b) {
    if (std::holds_alternative<typename bexpr::BTrue>(b.v())) {
      return f;
    } else if (std::holds_alternative<typename bexpr::BFalse>(b.v())) {
      return f0;
    } else if (std::holds_alternative<typename bexpr::BEq>(b.v())) {
      const auto &[a0, a1] = std::get<typename bexpr::BEq>(b.v());
      return f1(*a0, *a1);
    } else if (std::holds_alternative<typename bexpr::BLt>(b.v())) {
      const auto &[a0, a1] = std::get<typename bexpr::BLt>(b.v());
      return f2(*a0, *a1);
    } else if (std::holds_alternative<typename bexpr::BAnd>(b.v())) {
      const auto &[a0, a1] = std::get<typename bexpr::BAnd>(b.v());
      return f3(*a0, bexpr_rect<T1>(f, f0, f1, f2, f3, f4, f5, *a0), *a1,
                bexpr_rect<T1>(f, f0, f1, f2, f3, f4, f5, *a1));
    } else if (std::holds_alternative<typename bexpr::BOr>(b.v())) {
      const auto &[a0, a1] = std::get<typename bexpr::BOr>(b.v());
      return f4(*a0, bexpr_rect<T1>(f, f0, f1, f2, f3, f4, f5, *a0), *a1,
                bexpr_rect<T1>(f, f0, f1, f2, f3, f4, f5, *a1));
    } else {
      const auto &[a0] = std::get<typename bexpr::BNot>(b.v());
      return f5(*a0, bexpr_rect<T1>(f, f0, f1, f2, f3, f4, f5, *a0));
    }
  }

  template <typename T1, typename F2, typename F3, typename F4, typename F5,
            typename F6>
    requires std::is_invocable_r_v<T1, F2 &, expr &, expr &> &&
             std::is_invocable_r_v<T1, F3 &, expr &, expr &> &&
             std::is_invocable_r_v<T1, F4 &, bexpr &, T1 &, bexpr &, T1 &> &&
             std::is_invocable_r_v<T1, F5 &, bexpr &, T1 &, bexpr &, T1 &> &&
             std::is_invocable_r_v<T1, F6 &, bexpr &, T1 &>
  static T1 bexpr_rec(T1 f, T1 f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4, F6 &&f5,
                      const bexpr &b) {
    if (std::holds_alternative<typename bexpr::BTrue>(b.v())) {
      return f;
    } else if (std::holds_alternative<typename bexpr::BFalse>(b.v())) {
      return f0;
    } else if (std::holds_alternative<typename bexpr::BEq>(b.v())) {
      const auto &[a0, a1] = std::get<typename bexpr::BEq>(b.v());
      return f1(*a0, *a1);
    } else if (std::holds_alternative<typename bexpr::BLt>(b.v())) {
      const auto &[a0, a1] = std::get<typename bexpr::BLt>(b.v());
      return f2(*a0, *a1);
    } else if (std::holds_alternative<typename bexpr::BAnd>(b.v())) {
      const auto &[a0, a1] = std::get<typename bexpr::BAnd>(b.v());
      return f3(*a0, bexpr_rec<T1>(f, f0, f1, f2, f3, f4, f5, *a0), *a1,
                bexpr_rec<T1>(f, f0, f1, f2, f3, f4, f5, *a1));
    } else if (std::holds_alternative<typename bexpr::BOr>(b.v())) {
      const auto &[a0, a1] = std::get<typename bexpr::BOr>(b.v());
      return f4(*a0, bexpr_rec<T1>(f, f0, f1, f2, f3, f4, f5, *a0), *a1,
                bexpr_rec<T1>(f, f0, f1, f2, f3, f4, f5, *a1));
    } else {
      const auto &[a0] = std::get<typename bexpr::BNot>(b.v());
      return f5(*a0, bexpr_rec<T1>(f, f0, f1, f2, f3, f4, f5, *a0));
    }
  }

  static uint64_t expr_size(const expr &e);
  static uint64_t bexpr_size(const bexpr &b);
  static uint64_t stmt_size(const stmt &s);
  static inline const expr test_expr = expr::eadd(
      expr::ENum_(UINT64_C(1)),
      expr::emul(expr::ENum_(UINT64_C(2)), expr::ENum_(UINT64_C(3))));
  static inline const bexpr test_bexpr = bexpr::band(
      bexpr::beq(expr::evar(UINT64_C(0)), expr::ENum_(UINT64_C(5))),
      bexpr::blt(expr::evar(UINT64_C(1)), expr::ENum_(UINT64_C(10))));
  static inline const stmt test_stmt = stmt::sseq(
      stmt::sassign(UINT64_C(0), expr::ENum_(UINT64_C(42))),
      stmt::sif(bexpr::beq(expr::evar(UINT64_C(0)), expr::ENum_(UINT64_C(42))),
                stmt::sskip(),
                stmt::sassign(UINT64_C(0), expr::ENum_(UINT64_C(0)))));
  static inline const uint64_t test_expr_size = expr_size(test_expr);
  static inline const uint64_t test_bexpr_size = bexpr_size(test_bexpr);
  static inline const uint64_t test_stmt_size = stmt_size(test_stmt);
};

#endif // INCLUDED_LARGE_MUTUAL
