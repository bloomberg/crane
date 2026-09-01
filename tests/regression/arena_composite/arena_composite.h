#ifndef INCLUDED_ARENA_COMPOSITE
#define INCLUDED_ARENA_COMPOSITE

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#define CRANE_ARENA 1
#include "arena.h"
#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>

struct Nat;
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
    std::shared_ptr<Nat> _head{};
    std::shared_ptr<Nat> *_write = &_head;
    const Nat *_loop_self = this;
    Nat _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        *_write = std::make_shared<Nat>(std::move(_loop_m));
        break;
      } else {
        const auto &[a0] = std::get<typename Nat::S>(_sv.v());
        auto _cell = std::make_shared<Nat>(typename Nat::S(nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename Nat::S>((*_write)->v_mut()).a0;
        _loop_self = crane_raw(a0);
        continue;
      }
    }
    return std::move(*_head);
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
      const expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const expr *_self;
      };

      /// _After_Add: saves [a0, _s1], dispatches next recursive call.
      struct _After_Add {
        expr *a0;
        std::decay_t<decltype(Nat::s(Nat::o()))> _s1;
      };

      /// _Combine_Add: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Add {
        Nat _result;
        std::decay_t<decltype(Nat::s(Nat::o()))> _s1;
      };

      using _Frame = std::variant<_Enter, _After_Add, _Combine_Add>;
      Nat _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified esize: _Enter -> _After_Add -> _Combine_Add.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
            _result = Nat::s(Nat::o());
          } else {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_After_Add{crane_raw(a0), Nat::s(Nat::o())});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else if (std::holds_alternative<_After_Add>(_frame)) {
          auto _f = std::move(std::get<_After_Add>(_frame));
          _stack.emplace_back(_Combine_Add{std::move(_result), _f._s1});
          _stack.emplace_back(_Enter{_f.a0});
        } else {
          auto _f = std::move(std::get<_Combine_Add>(_frame));
          _result = _f._s1.add(std::move(_result)).add(std::move(_f._result));
        }
      }
      return _result;
    }

    Nat eval() const {
      const expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const expr *_self;
      };

      /// _After_Add: saves [a0], dispatches next recursive call.
      struct _After_Add {
        expr *a0;
      };

      /// _Combine_Add: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Add {
        Nat _result;
      };

      using _Frame = std::variant<_Enter, _After_Add, _Combine_Add>;
      Nat _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified eval: _Enter -> _After_Add -> _Combine_Add.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Lit>(_sv.v());
            _result = std::move(a0);
          } else {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_After_Add{crane_raw(a0)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else if (std::holds_alternative<_After_Add>(_frame)) {
          auto _f = std::move(std::get<_After_Add>(_frame));
          _stack.emplace_back(_Combine_Add{std::move(_result)});
          _stack.emplace_back(_Enter{_f.a0});
        } else {
          auto _f = std::move(std::get<_Combine_Add>(_frame));
          _result = std::move(_result).add(std::move(_f._result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, Nat &> &&
               std::is_invocable_r_v<T1, F1 &, expr &, T1 &, expr &, T1 &>
    T1 expr_rec(F0 &&f, F1 &&f0) const {
      const expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const expr *_self;
      };

      /// _After_Add: saves [a0_0, a1, a0_1], dispatches next recursive call.
      struct _After_Add {
        expr *a0_0;
        expr a1;
        expr a0_1;
      };

      /// _Combine_Add: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Add {
        std::decay_t<T1> _result;
        expr a1;
        expr a0;
      };

      using _Frame = std::variant<_Enter, _After_Add, _Combine_Add>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified expr_rec: _Enter -> _After_Add -> _Combine_Add.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Lit>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_After_Add{crane_raw(a0), *a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else if (std::holds_alternative<_After_Add>(_frame)) {
          auto _f = std::move(std::get<_After_Add>(_frame));
          _stack.emplace_back(_Combine_Add{std::move(_result), std::move(_f.a1),
                                           std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else {
          auto _f = std::move(std::get<_Combine_Add>(_frame));
          _result = f0(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f._result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, Nat &> &&
               std::is_invocable_r_v<T1, F1 &, expr &, T1 &, expr &, T1 &>
    T1 expr_rect(F0 &&f, F1 &&f0) const {
      const expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const expr *_self;
      };

      /// _After_Add: saves [a0_0, a1, a0_1], dispatches next recursive call.
      struct _After_Add {
        expr *a0_0;
        expr a1;
        expr a0_1;
      };

      /// _Combine_Add: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Add {
        std::decay_t<T1> _result;
        expr a1;
        expr a0;
      };

      using _Frame = std::variant<_Enter, _After_Add, _Combine_Add>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified expr_rect: _Enter -> _After_Add -> _Combine_Add.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Lit>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_After_Add{crane_raw(a0), *a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else if (std::holds_alternative<_After_Add>(_frame)) {
          auto _f = std::move(std::get<_After_Add>(_frame));
          _stack.emplace_back(_Combine_Add{std::move(_result), std::move(_f.a1),
                                           std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else {
          auto _f = std::move(std::get<_Combine_Add>(_frame));
          _result = f0(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f._result));
        }
      }
      return _result;
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
      const avl *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const avl *_self;
      };

      /// _After_Node: saves [a0, _s1], dispatches next recursive call.
      struct _After_Node {
        avl *a0;
        std::decay_t<decltype(Nat::s(Nat::o()))> _s1;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        Nat _result;
        std::decay_t<decltype(Nat::s(Nat::o()))> _s1;
      };

      using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
      Nat _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified size: _Enter -> _After_Node -> _Combine_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const avl *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename avl::Leaf>(_sv.v())) {
            _result = Nat::o();
          } else {
            const auto &[a0, a1, a2, a3, a4] =
                std::get<typename avl::Node>(_sv.v());
            _stack.emplace_back(_After_Node{crane_raw(a0), Nat::s(Nat::o())});
            _stack.emplace_back(_Enter{crane_raw(a3)});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{std::move(_result), _f._s1});
          _stack.emplace_back(_Enter{_f.a0});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = _f._s1.add(std::move(_result)).add(std::move(_f._result));
        }
      }
      return _result;
    }

    expr find(const Nat &k) const {
      const avl *_loop_self = this;
      while (true) {
        auto &&_sv = *_loop_self;
        if (std::holds_alternative<typename avl::Leaf>(_sv.v())) {
          return expr::lit(Nat::o());
        } else {
          const auto &[a0, a1, a2, a3, a4] =
              std::get<typename avl::Node>(_sv.v());
          switch (PeanoNat::ltb(k, a1)) {
          case Bool0::TRUE_: {
            _loop_self = crane_raw(a0);
            break;
          }
          case Bool0::FALSE_: {
            switch (PeanoNat::ltb(a1, k)) {
            case Bool0::TRUE_: {
              _loop_self = crane_raw(a3);
              break;
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
    }

    avl insert(Nat k, expr v) const {
      const avl *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const avl *_self;
        Nat k;
        expr v;
      };

      /// _Resume_Node: saves [a3, a2, a1], resumes after recursive call with
      /// _result.
      struct _Resume_Node {
        avl a3;
        expr a2;
        Nat a1;
      };

      /// _Resume_Node_1: saves [a2, a1, a0], resumes after recursive call with
      /// _result.
      struct _Resume_Node_1 {
        expr a2;
        Nat a1;
        avl a0;
      };

      using _Frame = std::variant<_Enter, _Resume_Node, _Resume_Node_1>;
      avl _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self, std::move(k), std::move(v)});
      /// Loopified insert: _Enter -> _Resume_Node -> _Resume_Node_1.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const avl *_self = _f._self;
          Nat k = std::move(_f.k);
          expr v = std::move(_f.v);
          auto &&_sv = *_self;
          if (std::holds_alternative<typename avl::Leaf>(_sv.v())) {
            _result = avl::leaf().mk(std::move(k), std::move(v), avl::leaf());
          } else {
            const auto &[a0, a1, a2, a3, a4] =
                std::get<typename avl::Node>(_sv.v());
            switch (PeanoNat::ltb(k, a1)) {
            case Bool0::TRUE_: {
              _stack.emplace_back(_Resume_Node{*a3, a2, a1});
              _stack.emplace_back(
                  _Enter{crane_raw(a0), std::move(k), std::move(v)});
              break;
            }
            case Bool0::FALSE_: {
              switch (PeanoNat::ltb(a1, k)) {
              case Bool0::TRUE_: {
                _stack.emplace_back(_Resume_Node_1{a2, a1, *a0});
                _stack.emplace_back(
                    _Enter{crane_raw(a3), std::move(k), std::move(v)});
                break;
              }
              case Bool0::FALSE_: {
                _result = avl::node(*a0, std::move(k), std::move(v), *a3, a4);
                break;
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
        } else if (std::holds_alternative<_Resume_Node>(_frame)) {
          auto _f = std::move(std::get<_Resume_Node>(_frame));
          _result = std::move(_result).balance(
              std::move(_f.a1), std::move(_f.a2), std::move(_f.a3));
        } else {
          auto _f = std::move(std::get<_Resume_Node_1>(_frame));
          _result = std::move(_f.a0).balance(std::move(_f.a1), std::move(_f.a2),
                                             std::move(_result));
        }
      }
      return _result;
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
      const avl *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const avl *_self;
      };

      /// _After_Node: saves [a2_0, a6, a5, a4, a3, a2_1], dispatches next
      /// recursive call.
      struct _After_Node {
        avl *a2_0;
        Nat a6;
        avl a5;
        expr a4;
        Nat a3;
        avl a2_1;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        std::decay_t<T1> _result;
        Nat a6;
        avl a5;
        expr a4;
        Nat a3;
        avl a2;
      };

      using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified avl_rec: _Enter -> _After_Node -> _Combine_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const avl *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename avl::Leaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a2, a3, a4, a5, a6] =
                std::get<typename avl::Node>(_sv.v());
            _stack.emplace_back(
                _After_Node{crane_raw(a2), a6, *a5, a4, a3, *a2});
            _stack.emplace_back(_Enter{crane_raw(a5)});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{
              std::move(_result), std::move(_f.a6), std::move(_f.a5),
              std::move(_f.a4), std::move(_f.a3), std::move(_f.a2_1)});
          _stack.emplace_back(_Enter{_f.a2_0});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = f0(std::move(_f.a2), std::move(_result), std::move(_f.a3),
                       std::move(_f.a4), std::move(_f.a5),
                       std::move(_f._result), std::move(_f.a6));
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, avl &, T1 &, Nat &, expr &,
                                     avl &, T1 &, Nat &>
    T1 avl_rect(T1 f, F1 &&f0) const {
      const avl *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const avl *_self;
      };

      /// _After_Node: saves [a2_0, a6, a5, a4, a3, a2_1], dispatches next
      /// recursive call.
      struct _After_Node {
        avl *a2_0;
        Nat a6;
        avl a5;
        expr a4;
        Nat a3;
        avl a2_1;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        std::decay_t<T1> _result;
        Nat a6;
        avl a5;
        expr a4;
        Nat a3;
        avl a2;
      };

      using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified avl_rect: _Enter -> _After_Node -> _Combine_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const avl *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename avl::Leaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a2, a3, a4, a5, a6] =
                std::get<typename avl::Node>(_sv.v());
            _stack.emplace_back(
                _After_Node{crane_raw(a2), a6, *a5, a4, a3, *a2});
            _stack.emplace_back(_Enter{crane_raw(a5)});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{
              std::move(_result), std::move(_f.a6), std::move(_f.a5),
              std::move(_f.a4), std::move(_f.a3), std::move(_f.a2_1)});
          _stack.emplace_back(_Enter{_f.a2_0});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = f0(std::move(_f.a2), std::move(_result), std::move(_f.a3),
                       std::move(_f.a4), std::move(_f.a5),
                       std::move(_f._result), std::move(_f.a6));
        }
      }
      return _result;
    }
  };
};

#endif // INCLUDED_ARENA_COMPOSITE
