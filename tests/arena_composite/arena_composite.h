#ifndef INCLUDED_ARENA_COMPOSITE
#define INCLUDED_ARENA_COMPOSITE

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#define CRANE_ARENA 1
#include "arena.h"
#include "small_vector.h"
#include <atomic>

enum class Bool0 { TRUE_, FALSE_ };

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Nat() {}

  explicit Nat(O _v) : v_(_v) {}

  explicit Nat(S _v) : v_(std::move(_v)) {}

  static Nat o() { return Nat(O{}); }

  static Nat s(Nat a0) {
    return Nat(S{crane::arena_make_shared<Nat>(std::move(a0))});
  }

  // MANIPULATORS
  ~Nat() {
    crane::small_vector<std::shared_ptr<Nat>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
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

  Nat(const Nat &) = default;
  Nat &operator=(const Nat &) = default;
  Nat(Nat &&) noexcept = default;
  Nat &operator=(Nat &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  Nat add(Nat m) const {
    if (std::holds_alternative<typename Nat::O>(this->v())) {
      return m;
    } else {
      const auto &[a0] = std::get<typename Nat::S>(this->v());
      return Nat::s(a0->add(std::move(m)));
    }
  }
};

struct PeanoNat {
  static Bool0 leb(const Nat &n, const Nat &m);
  static Bool0 ltb(Nat n, const Nat &m);
  static Nat max(Nat n, Nat m);
};

struct Comp {
  struct expr {
    // TYPES
    struct Lit {
      Nat a0;
    };

    struct Add {
      std::shared_ptr<expr> a0;
      std::shared_ptr<expr> a1;
    };

    using variant_t = std::variant<Lit, Add>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    expr() {}

    explicit expr(Lit _v) : v_(std::move(_v)) {}

    explicit expr(Add _v) : v_(std::move(_v)) {}

    static expr lit(Nat a0) { return expr(Lit{std::move(a0)}); }

    static expr add(expr a0, expr a1) {
      return expr(Add{crane::arena_make_shared<expr>(std::move(a0)),
                      crane::arena_make_shared<expr>(std::move(a1))});
    }

    // MANIPULATORS
    ~expr() {
      crane::small_vector<std::shared_ptr<expr>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Add>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
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

    expr(const expr &) = default;
    expr &operator=(const expr &) = default;
    expr(expr &&) noexcept = default;
    expr &operator=(expr &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    Nat esize() const {
      if (std::holds_alternative<typename expr::Lit>(this->v())) {
        return Nat::s(Nat::o());
      } else {
        const auto &[a0, a1] = std::get<typename expr::Add>(this->v());
        return Nat::s(Nat::o()).add(a0->esize()).add(a1->esize());
      }
    }

    Nat eval() const {
      if (std::holds_alternative<typename expr::Lit>(this->v())) {
        const auto &[a0] = std::get<typename expr::Lit>(this->v());
        return a0;
      } else {
        const auto &[a0, a1] = std::get<typename expr::Add>(this->v());
        return a0->eval().add(a1->eval());
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, Nat &> &&
               std::is_invocable_r_v<T1, F1 &, expr &, T1 &, expr &, T1 &>
    T1 expr_rec(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename expr::Lit>(this->v())) {
        const auto &[a0] = std::get<typename expr::Lit>(this->v());
        return f(a0);
      } else {
        const auto &[a0, a1] = std::get<typename expr::Add>(this->v());
        return f0(*a0, a0->template expr_rec<T1>(f, f0), *a1,
                  a1->template expr_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, Nat &> &&
               std::is_invocable_r_v<T1, F1 &, expr &, T1 &, expr &, T1 &>
    T1 expr_rect(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename expr::Lit>(this->v())) {
        const auto &[a0] = std::get<typename expr::Lit>(this->v());
        return f(a0);
      } else {
        const auto &[a0, a1] = std::get<typename expr::Add>(this->v());
        return f0(*a0, a0->template expr_rect<T1>(f, f0), *a1,
                  a1->template expr_rect<T1>(f, f0));
      }
    }
  };

  struct avl {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<avl> a0;
      Nat a1;
      expr a2;
      std::shared_ptr<avl> a3;
      Nat a4;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    avl() {}

    explicit avl(Leaf _v) : v_(_v) {}

    explicit avl(Node _v) : v_(std::move(_v)) {}

    static avl leaf() { return avl(Leaf{}); }

    static avl node(avl a0, Nat a1, expr a2, avl a3, Nat a4) {
      return avl(Node{crane::arena_make_shared<avl>(std::move(a0)),
                      std::move(a1), std::move(a2),
                      crane::arena_make_shared<avl>(std::move(a3)),
                      std::move(a4)});
    }

    // MANIPULATORS
    ~avl() {
      crane::small_vector<std::shared_ptr<avl>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a3) {
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

    avl(const avl &) = default;
    avl &operator=(const avl &) = default;
    avl(avl &&) noexcept = default;
    avl &operator=(avl &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    Nat size() const {
      if (std::holds_alternative<typename avl::Leaf>(this->v())) {
        return Nat::o();
      } else {
        const auto &[a0, a1, a2, a3, a4] =
            std::get<typename avl::Node>(this->v());
        return Nat::s(Nat::o()).add(a0->size()).add(a3->size());
      }
    }

    expr find(const Nat &k) const {
      if (std::holds_alternative<typename avl::Leaf>(this->v())) {
        return expr::lit(Nat::o());
      } else {
        const auto &[a0, a1, a2, a3, a4] =
            std::get<typename avl::Node>(this->v());
        switch (PeanoNat::ltb(k, a1)) {
        case Bool0::TRUE_: {
          return a0->find(k);
        }
        case Bool0::FALSE_: {
          switch (PeanoNat::ltb(a1, k)) {
          case Bool0::TRUE_: {
            return a3->find(k);
          }
          case Bool0::FALSE_: {
            return a2;
          }
          default:
            std::unreachable();
          }
          break;
        }
        default:
          std::unreachable();
        }
      }
    }

    avl insert(Nat k, expr v) const {
      if (std::holds_alternative<typename avl::Leaf>(this->v())) {
        return avl::leaf().mk(std::move(k), std::move(v), avl::leaf());
      } else {
        const auto &[a0, a1, a2, a3, a4] =
            std::get<typename avl::Node>(this->v());
        switch (PeanoNat::ltb(k, a1)) {
        case Bool0::TRUE_: {
          return a0->insert(std::move(k), std::move(v)).balance(a1, a2, *a3);
        }
        case Bool0::FALSE_: {
          switch (PeanoNat::ltb(a1, k)) {
          case Bool0::TRUE_: {
            return a0->balance(a1, a2, a3->insert(std::move(k), std::move(v)));
          }
          case Bool0::FALSE_: {
            return avl::node(*a0, std::move(k), std::move(v), *a3, a4);
          }
          default:
            std::unreachable();
          }
          break;
        }
        default:
          std::unreachable();
        }
      }
    }

    avl balance(const Nat &k, const expr &v, const avl &r) const {
      Nat hl = this->height();
      Nat hr = r.height();
      switch (PeanoNat::ltb(Nat::s(Nat::s(hr)), hl)) {
      case Bool0::TRUE_: {
        return this->rotate_right(k, v, r);
      }
      case Bool0::FALSE_: {
        switch (PeanoNat::ltb(Nat::s(Nat::s(std::move(hl))), std::move(hr))) {
        case Bool0::TRUE_: {
          return this->rotate_left(k, v, r);
        }
        case Bool0::FALSE_: {
          return this->mk(k, v, r);
        }
        default:
          std::unreachable();
        }
        break;
      }
      default:
        std::unreachable();
      }
    }

    avl rotate_left(const Nat &k, const expr &v, const avl &r) const {
      if (std::holds_alternative<typename avl::Leaf>(r.v())) {
        return this->mk(k, v, r);
      } else {
        const auto &[a0, a1, a2, a3, a4] = std::get<typename avl::Node>(r.v());
        return this->mk(k, v, *a0).mk(a1, a2, *a3);
      }
    }

    avl rotate_right(const Nat &k, const expr &v, const avl &r) const {
      if (std::holds_alternative<typename avl::Leaf>(this->v())) {
        return this->mk(k, v, r);
      } else {
        const auto &[a0, a1, a2, a3, a4] =
            std::get<typename avl::Node>(this->v());
        return a0->mk(a1, a2, a3->mk(k, v, r));
      }
    }

    avl mk(Nat k, expr v, avl r) const {
      return avl::node(
          *this, std::move(k), std::move(v), r,
          Nat::s(Nat::o()).add(PeanoNat::max(this->height(), r.height())));
    }

    Nat height() const {
      if (std::holds_alternative<typename avl::Leaf>(this->v())) {
        return Nat::o();
      } else {
        const auto &[a0, a1, a2, a3, a4] =
            std::get<typename avl::Node>(this->v());
        return a4;
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, avl &, T1 &, Nat &, expr &,
                                     avl &, T1 &, Nat &>
    T1 avl_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename avl::Leaf>(this->v())) {
        return f;
      } else {
        const auto &[a2, a3, a4, a5, a6] =
            std::get<typename avl::Node>(this->v());
        return f0(*a2, a2->template avl_rec<T1>(f, f0), a3, a4, *a5,
                  a5->template avl_rec<T1>(f, f0), a6);
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, avl &, T1 &, Nat &, expr &,
                                     avl &, T1 &, Nat &>
    T1 avl_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename avl::Leaf>(this->v())) {
        return f;
      } else {
        const auto &[a2, a3, a4, a5, a6] =
            std::get<typename avl::Node>(this->v());
        return f0(*a2, a2->template avl_rect<T1>(f, f0), a3, a4, *a5,
                  a5->template avl_rect<T1>(f, f0), a6);
      }
    }
  };
};

#endif // INCLUDED_ARENA_COMPOSITE
