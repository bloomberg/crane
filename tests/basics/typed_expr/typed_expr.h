#ifndef INCLUDED_TYPED_EXPR
#define INCLUDED_TYPED_EXPR

#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <utility>
#include <variant>

enum class Ty;
struct Expr;
enum class Ty { TNAT, TBOOL };

struct Expr {
  // TYPES
  struct ENat {
    uint64_t a0;
  };

  struct EBool {
    bool a0;
  };

  struct EAdd {
    std::shared_ptr<Expr> a0;
    std::shared_ptr<Expr> a1;
  };

  struct EEq {
    std::shared_ptr<Expr> a0;
    std::shared_ptr<Expr> a1;
  };

  struct EIf {
    Ty t;
    std::shared_ptr<Expr> a1;
    std::shared_ptr<Expr> a2;
    std::shared_ptr<Expr> a3;
  };

  using variant_t = std::variant<ENat, EBool, EAdd, EEq, EIf>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Expr() {}

  explicit Expr(ENat _v) : v_(std::move(_v)) {}

  explicit Expr(EBool _v) : v_(std::move(_v)) {}

  explicit Expr(EAdd _v) : v_(std::move(_v)) {}

  explicit Expr(EEq _v) : v_(std::move(_v)) {}

  explicit Expr(EIf _v) : v_(std::move(_v)) {}

  static Expr enat(uint64_t a0) { return Expr(ENat{a0}); }

  static Expr ebool(bool a0) { return Expr(EBool{a0}); }

  static Expr eadd(Expr a0, Expr a1) {
    return Expr(EAdd{std::make_shared<Expr>(std::move(a0)),
                     std::make_shared<Expr>(std::move(a1))});
  }

  static Expr eeq(Expr a0, Expr a1) {
    return Expr(EEq{std::make_shared<Expr>(std::move(a0)),
                    std::make_shared<Expr>(std::move(a1))});
  }

  static Expr eif(Ty t, Expr a1, Expr a2, Expr a3) {
    return Expr(EIf{t, std::make_shared<Expr>(std::move(a1)),
                    std::make_shared<Expr>(std::move(a2)),
                    std::make_shared<Expr>(std::move(a3))});
  }

  // MANIPULATORS
  ~Expr() {
    if (std::holds_alternative<ENat>(v_mut())) {
      return;
    }
    if (std::holds_alternative<EBool>(v_mut())) {
      return;
    }
    if (auto *_alt = std::get_if<EAdd>(&v_mut())) {
      if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
            (_alt->a1 && _alt->a1.use_count() == 1))) {
        return;
      }
    }
    if (auto *_alt = std::get_if<EEq>(&v_mut())) {
      if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
            (_alt->a1 && _alt->a1.use_count() == 1))) {
        return;
      }
    }
    if (auto *_alt = std::get_if<EIf>(&v_mut())) {
      if (!((_alt->a1 && _alt->a1.use_count() == 1) ||
            (_alt->a2 && _alt->a2.use_count() == 1) ||
            (_alt->a3 && _alt->a3.use_count() == 1))) {
        return;
      }
    }
    crane::small_vector<std::shared_ptr<Expr>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<EAdd>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          _stack.push_back(std::move(_alt->a0));
        }
        if (_alt->a1 && _alt->a1.use_count() == 1) {
          _stack.push_back(std::move(_alt->a1));
        }
      }
      if (auto *_alt = std::get_if<EEq>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          _stack.push_back(std::move(_alt->a0));
        }
        if (_alt->a1 && _alt->a1.use_count() == 1) {
          _stack.push_back(std::move(_alt->a1));
        }
      }
      if (auto *_alt = std::get_if<EIf>(&_v)) {
        if (_alt->a1 && _alt->a1.use_count() == 1) {
          _stack.push_back(std::move(_alt->a1));
        }
        if (_alt->a2 && _alt->a2.use_count() == 1) {
          _stack.push_back(std::move(_alt->a2));
        }
        if (_alt->a3 && _alt->a3.use_count() == 1) {
          _stack.push_back(std::move(_alt->a3));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        std::atomic_thread_fence(std::memory_order_acquire);
        _drain(_cur->v_mut());
      }
    }
  }

  Expr(const Expr &) = default;
  Expr &operator=(const Expr &) = default;
  Expr(Expr &&) = default;
  Expr &operator=(Expr &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  crane::obj eval(Ty) const;
};

inline crane::obj Expr::eval(Ty) const {
  if (std::holds_alternative<typename Expr::ENat>(this->v())) {
    const auto &[a0] = std::get<typename Expr::ENat>(this->v());
    return a0;
  } else if (std::holds_alternative<typename Expr::EBool>(this->v())) {
    const auto &[a0] = std::get<typename Expr::EBool>(this->v());
    return a0;
  } else if (std::holds_alternative<typename Expr::EAdd>(this->v())) {
    const auto &[a0, a1] = std::get<typename Expr::EAdd>(this->v());
    return (crane::any_cast<uint64_t>(a0->eval(Ty::TNAT)) +
            crane::any_cast<uint64_t>(a1->eval(Ty::TNAT)));
  } else if (std::holds_alternative<typename Expr::EEq>(this->v())) {
    const auto &[a0, a1] = std::get<typename Expr::EEq>(this->v());
    return crane::any_cast<uint64_t>(a0->eval(Ty::TNAT)) ==
           crane::any_cast<uint64_t>(a1->eval(Ty::TNAT));
  } else {
    const auto &[t, a1, a2, a3] = std::get<typename Expr::EIf>(this->v());
    if (crane::any_cast<bool>(a1->eval(Ty::TBOOL))) {
      return a2->eval(t);
    } else {
      return a3->eval(t);
    }
  }
}

#endif // INCLUDED_TYPED_EXPR
