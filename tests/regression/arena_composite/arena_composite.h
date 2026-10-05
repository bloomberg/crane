#ifndef INCLUDED_ARENA_COMPOSITE
#define INCLUDED_ARENA_COMPOSITE

#include <atomic>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#define CRANE_ARENA 1
#include "arena.h"
#include "crane_fn.h"
#include "small_vector.h"

enum class Bool0;
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
    auto _next = [&](variant_t &_v) -> std::shared_ptr<Nat> {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      return nullptr;
    };
    std::shared_ptr<Nat> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  Nat(const Nat &) = default;
  Nat &operator=(const Nat &) = default;
  Nat(Nat &&) = default;
  Nat &operator=(Nat &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  Nat add(Nat m) const {
    std::optional<Nat> _root{};
    std::shared_ptr<Nat> *_write = nullptr;
    const Nat *_loop_self = this;
    Nat _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        auto _value = std::move(_loop_m);
        (_write ? *(*_write = std::make_shared<Nat>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0] = std::get<typename Nat::S>(_sv.v());
        auto _cell = typename Nat::S(nullptr);
        Nat &_node =
            (_write ? *(*_write = std::make_shared<Nat>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename Nat::S>(_node.v_mut()).a0;
        _loop_self = crane_raw(a0);
        continue;
      }
    }
    return std::move(*_root);
  }
};

struct PeanoNat {
  static Bool0 leb(const Nat &n, const Nat &m);
  static Bool0 ltb(const Nat &n, const Nat &m);
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
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
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
    expr(expr &&) = default;
    expr &operator=(expr &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    Nat esize() const {
      const expr *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const expr *_self;
      };

      /// CraneCont_Add: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Add {
        std::shared_ptr<expr> a1;
      };

      /// CraneCont_Add_1: saves [_tmp2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Add_1 {
        Nat _tmp2;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Add, CraneCont_Add_1>;
      Nat _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified esize: CraneEnter -> CraneCont_Add -> CraneCont_Add_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
            _result = Nat::s(Nat::o());
          } else {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(CraneCont_Add{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Add>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Add>(_frame));
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_Add_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<CraneCont_Add_1>(_frame));
          _result =
              Nat::s(Nat::o()).add(std::move(_f._tmp2)).add(std::move(_result));
        }
      }
      return _result;
    }

    Nat eval() const {
      const expr *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const expr *_self;
      };

      /// CraneCont_Add: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Add {
        std::shared_ptr<expr> a1;
      };

      /// CraneCont_Add_1: saves [_tmp2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Add_1 {
        Nat _tmp2;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Add, CraneCont_Add_1>;
      Nat _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified eval: CraneEnter -> CraneCont_Add -> CraneCont_Add_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Lit>(_sv.v());
            _result = std::move(a0);
          } else {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(CraneCont_Add{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Add>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Add>(_frame));
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_Add_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<CraneCont_Add_1>(_frame));
          _result = std::move(_f._tmp2).add(std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
    T1 expr_rec(F0 &&f, F1 &&f0) const {
      return this->template expr_rect<T1>(f, f0);
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, const Nat &>
    T1 expr_rect(F0 &&f, F1 &&f0) const {
      const expr *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const expr *_self;
      };

      /// CraneCont_Add: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Add {
        std::shared_ptr<expr> a0;
        std::shared_ptr<expr> a1;
      };

      /// CraneCont_Add_1: saves [_tmp2, a0, a1], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Add_1 {
        T1 _tmp2;
        std::shared_ptr<expr> a0;
        std::shared_ptr<expr> a1;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Add, CraneCont_Add_1>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified expr_rect: CraneEnter -> CraneCont_Add -> CraneCont_Add_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Lit>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(CraneCont_Add{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Add>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Add>(_frame));
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          _stack.emplace_back(
              CraneCont_Add_1{std::move(_result), std::move(a0), a1});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<CraneCont_Add_1>(_frame));
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          std::shared_ptr<expr> a1 = std::move(_f.a1);
          _result = f0(*a0, std::move(_f._tmp2), *a1, std::move(_result));
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
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
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

    avl(const avl &) = default;
    avl &operator=(const avl &) = default;
    avl(avl &&) = default;
    avl &operator=(avl &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    Nat size() const {
      const avl *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const avl *_self;
      };

      /// CraneCont_Node: saves [a3], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Node {
        std::shared_ptr<avl> a3;
      };

      /// CraneCont_Node_1: saves [_tmp2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Node_1 {
        Nat _tmp2;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
      Nat _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified size: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const avl *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename avl::Leaf>(_sv.v())) {
            _result = Nat::o();
          } else {
            const auto &[a0, a1, a2, a3, a4] =
                std::get<typename avl::Node>(_sv.v());
            _stack.emplace_back(CraneCont_Node{a3});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Node>(_frame));
          std::shared_ptr<avl> a3 = std::move(_f.a3);
          _stack.emplace_back(CraneCont_Node_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a3)});
        } else {
          auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
          _result =
              Nat::s(Nat::o()).add(std::move(_f._tmp2)).add(std::move(_result));
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

    avl insert(const Nat &k, const expr &v) const {
      const avl *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const avl *_self;
      };

      /// CraneCont_Node: saves [a1, a2, a3], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Node {
        Nat a1;
        expr a2;
        std::shared_ptr<avl> a3;
      };

      /// CraneCont_Node_1: saves [a0, a1, a2], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Node_1 {
        std::shared_ptr<avl> a0;
        Nat a1;
        expr a2;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
      avl _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified insert: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const avl *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename avl::Leaf>(_sv.v())) {
            _result = avl::leaf().mk(k, v, avl::leaf());
          } else {
            const auto &[a0, a1, a2, a3, a4] =
                std::get<typename avl::Node>(_sv.v());
            switch (PeanoNat::ltb(k, a1)) {
            case Bool0::TRUE_: {
              _stack.emplace_back(CraneCont_Node{a1, a2, a3});
              _stack.emplace_back(CraneEnter{crane_raw(a0)});
              break;
            }
            case Bool0::FALSE_: {
              switch (PeanoNat::ltb(a1, k)) {
              case Bool0::TRUE_: {
                _stack.emplace_back(CraneCont_Node_1{a0, a1, a2});
                _stack.emplace_back(CraneEnter{crane_raw(a3)});
                break;
              }
              case Bool0::FALSE_: {
                _result = avl::node(*a0, k, v, *a3, a4);
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
        } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Node>(_frame));
          Nat a1 = std::move(_f.a1);
          expr a2 = std::move(_f.a2);
          std::shared_ptr<avl> a3 = std::move(_f.a3);
          _result = std::move(_result).balance(a1, a2, *a3);
        } else {
          auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
          std::shared_ptr<avl> a0 = std::move(_f.a0);
          Nat a1 = std::move(_f.a1);
          expr a2 = std::move(_f.a2);
          _result = a0->balance(a1, a2, std::move(_result));
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

    avl mk(const Nat &k, const expr &v, const avl &r) const {
      return avl::node(
          *this, k, v, r,
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

    template <typename T1, typename F1> T1 avl_rec(T1 f, F1 &&f0) const {
      return this->template avl_rect<T1>(std::move(f), f0);
    }

    template <typename T1, typename F1> T1 avl_rect(T1 f, F1 &&f0) const {
      const avl *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const avl *_self;
      };

      /// CraneCont_Node: saves [a2, a3, a4, a5, a6], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_Node {
        std::shared_ptr<avl> a2;
        Nat a3;
        expr a4;
        std::shared_ptr<avl> a5;
        Nat a6;
      };

      /// CraneCont_Node_1: saves [_tmp2, a2, a3, a4, a5, a6], resumes after
      /// recursive call, then processes rest.
      struct CraneCont_Node_1 {
        T1 _tmp2;
        std::shared_ptr<avl> a2;
        Nat a3;
        expr a4;
        std::shared_ptr<avl> a5;
        Nat a6;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified avl_rect: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const avl *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename avl::Leaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a2, a3, a4, a5, a6] =
                std::get<typename avl::Node>(_sv.v());
            _stack.emplace_back(CraneCont_Node{a2, a3, a4, a5, a6});
            _stack.emplace_back(CraneEnter{crane_raw(a2)});
          }
        } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Node>(_frame));
          std::shared_ptr<avl> a2 = std::move(_f.a2);
          Nat a3 = std::move(_f.a3);
          expr a4 = std::move(_f.a4);
          std::shared_ptr<avl> a5 = std::move(_f.a5);
          Nat a6 = std::move(_f.a6);
          _stack.emplace_back(
              CraneCont_Node_1{std::move(_result), std::move(a2), std::move(a3),
                               std::move(a4), a5, std::move(a6)});
          _stack.emplace_back(CraneEnter{crane_raw(a5)});
        } else {
          auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
          std::shared_ptr<avl> a2 = std::move(_f.a2);
          Nat a3 = std::move(_f.a3);
          expr a4 = std::move(_f.a4);
          std::shared_ptr<avl> a5 = std::move(_f.a5);
          Nat a6 = std::move(_f.a6);
          _result =
              f0(*a2, std::move(_f._tmp2), a3, a4, *a5, std::move(_result), a6);
        }
      }
      return _result;
    }
  };
};

#endif // INCLUDED_ARENA_COMPOSITE
