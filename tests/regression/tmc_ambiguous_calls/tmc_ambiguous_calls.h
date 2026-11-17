#ifndef INCLUDED_TMC_AMBIGUOUS_CALLS
#define INCLUDED_TMC_AMBIGUOUS_CALLS

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

/// Recursive functions where one constructor holds several recursive calls.
/// Tail modulo cons can continue by only one of them, so these are lowered
/// with an explicit frame stack instead, and must not overflow the C++
/// stack on deep inputs.
struct TmcAmbiguousCalls {
  /// The OCaml manual's example: the definition sits in a pair, the body is a
  /// direct constructor argument.
  struct exp {
    // TYPES
    struct Var {
      uint64_t v_0;
    };

    struct Let {
      std::shared_ptr<std::pair<uint64_t, exp>> b;
      std::shared_ptr<exp> body;
    };

    using variant_t = std::variant<Var, Let>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    exp() {}

    explicit exp(Var _v) : v_(std::move(_v)) {}

    explicit exp(Let _v) : v_(std::move(_v)) {}

    static exp var(uint64_t v_0) { return exp(Var{v_0}); }

    static exp let(std::pair<uint64_t, exp> b, exp body) {
      return exp(Let{std::make_shared<std::pair<uint64_t, exp>>(std::move(b)),
                     std::make_shared<exp>(std::move(body))});
    }

    // MANIPULATORS
    ~exp() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<Var>(v_mut())) {
        return;
      }
      crane::small_vector<std::shared_ptr<exp>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Let>(&_v)) {
          if (_alt->b && _alt->b.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            _stack.push_back(std::make_shared<exp>(std::move(_alt->b->second)));
            _alt->b.reset();
          }
          if (_alt->body && _alt->body.use_count() == 1) {
            _stack.push_back(std::move(_alt->body));
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

    exp(const exp &) = default;
    exp &operator=(const exp &) = default;
    exp(exp &&) = default;
    exp &operator=(exp &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename F0>
      requires std::is_invocable_r_v<uint64_t, F0 &, const uint64_t &> &&
               std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
    exp map_vars(F0 &&f) const {
      const exp *_self = this;

      // Explicit stack replaces the non-tail recursion of map_vars: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const exp *_self;
      };

      struct _after_map_vars_in_pair {
        const exp *body0;
        uint64_t v;
      };

      struct _after_map_vars_in_pair_2 {
        uint64_t v;
        exp _tmp2;
      };

      using _frame = std::variant<_call, _after_map_vars_in_pair,
                                  _after_map_vars_in_pair_2>;
      exp _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const exp *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename exp::Var>(_sv.v())) {
            const auto &[v_0] = std::get<typename exp::Var>(_sv.v());
            _result = exp::var(f(v_0));
          } else {
            const auto &[b0, body0] = std::get<typename exp::Let>(_sv.v());
            const auto &[v, def] = (*b0);
            _stack.emplace_back(_after_map_vars_in_pair{crane_raw(body0), v});
            _stack.emplace_back(_call{&def});
          }
        } else if (std::holds_alternative<_after_map_vars_in_pair>(_popped)) {
          auto _f = std::move(std::get<_after_map_vars_in_pair>(_popped));
          _stack.pop_back();
          const exp &body0 = *_f.body0;
          uint64_t v = _f.v;
          _stack.emplace_back(_after_map_vars_in_pair_2{v, std::move(_result)});
          _stack.emplace_back(_call{_f.body0});
        } else {
          auto _f = std::move(std::get<_after_map_vars_in_pair_2>(_popped));
          _stack.pop_back();
          uint64_t v = _f.v;
          _result = exp::let(std::make_pair(f(v), std::move(_f._tmp2)),
                             std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
    T1 exp_rec(F0 &&f, F1 &&f0) const {
      return this->template exp_rect<T1>(f, f0);
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
    T1 exp_rect(F0 &&f, F1 &&f0) const {
      const exp *_self = this;

      // Explicit stack replaces the non-tail recursion of exp_rect: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const exp *_self;
      };

      struct _after_exp_rect_in_Let {
        std::shared_ptr<std::pair<uint64_t, exp>> b0;
        std::shared_ptr<exp> body0;
      };

      using _frame = std::variant<_call, _after_exp_rect_in_Let>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const exp *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename exp::Var>(_sv.v())) {
            const auto &[v_0] = std::get<typename exp::Var>(_sv.v());
            _result = f(v_0);
          } else {
            const auto &[b0, body0] = std::get<typename exp::Let>(_sv.v());
            _stack.emplace_back(_after_exp_rect_in_Let{b0, body0});
            _stack.emplace_back(_call{crane_raw(body0)});
          }
        } else {
          auto _f = std::move(std::get<_after_exp_rect_in_Let>(_popped));
          _stack.pop_back();
          std::shared_ptr<std::pair<uint64_t, exp>> b0 = std::move(_f.b0);
          std::shared_ptr<exp> body0 = std::move(_f.body0);
          _result = f0(*b0, *body0, std::move(_result));
        }
      }
      return _result;
    }
  };

  /// The same with a separate binding type holding the definition.
  template <typename A> struct binding {
    // DATA
    uint64_t v_0;
    A def;

    // ACCESSORS
    binding<A> clone() const { return {v_0, def}; }

    template <typename CraneU> operator binding<CraneU>() const {
      return {v_0, [&]() -> CraneU {
        if constexpr (crane_convertible<CraneU, const A &>) {
          return crane_convert<CraneU>(def);
        } else {
          throw std::logic_error("unreachable: inactive constructor field at "
                                 "this instantiation");
        }
      }()};
    }

    // CREATORS
    static binding<A> bind(uint64_t v_0, A def) {
      return {v_0, std::move(def)};
    }

    template <typename T1, typename F0> T1 binding_rec(F0 &&f) const {
      return this->template binding_rect<T1>(f);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &, const A &>
    T1 binding_rect(F0 &&f) const {
      const auto &[v_0, def0] = *this;
      return f(v_0, def0);
    }
  };

  struct bexp {
    // TYPES
    struct BVar {
      uint64_t v_0;
    };

    struct BLet {
      std::shared_ptr<binding<bexp>> b;
      std::shared_ptr<bexp> body;
    };

    using variant_t = std::variant<BVar, BLet>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    bexp() {}

    explicit bexp(BVar _v) : v_(std::move(_v)) {}

    explicit bexp(BLet _v) : v_(std::move(_v)) {}

    static bexp bvar(uint64_t v_0) { return bexp(BVar{v_0}); }

    static bexp blet(binding<bexp> b, bexp body) {
      return bexp(BLet{std::make_shared<binding<bexp>>(std::move(b)),
                       std::make_shared<bexp>(std::move(body))});
    }

    // MANIPULATORS
    ~bexp() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<BVar>(v_mut())) {
        return;
      }
      crane::small_vector<std::shared_ptr<bexp>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<BLet>(&_v)) {
          if (_alt->b && _alt->b.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            _stack.push_back(std::make_shared<bexp>(std::move(_alt->b->def)));
            _alt->b.reset();
          }
          if (_alt->body && _alt->body.use_count() == 1) {
            _stack.push_back(std::move(_alt->body));
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

    bexp(const bexp &) = default;
    bexp &operator=(const bexp &) = default;
    bexp(bexp &&) = default;
    bexp &operator=(bexp &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename F0>
      requires std::is_invocable_r_v<uint64_t, F0 &, const uint64_t &> &&
               std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
    bexp map_bvars(F0 &&f) const {
      const bexp *_self = this;

      // Explicit stack replaces the non-tail recursion of map_bvars: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const bexp *_self;
      };

      struct _after_map_bvars_in_Bind {
        const bexp *body0;
        uint64_t v_00;
      };

      struct _after_map_bvars_in_Bind_2 {
        uint64_t v_00;
        bexp _tmp2;
      };

      using _frame = std::variant<_call, _after_map_bvars_in_Bind,
                                  _after_map_bvars_in_Bind_2>;
      bexp _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const bexp *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename bexp::BVar>(_sv.v())) {
            const auto &[v_0] = std::get<typename bexp::BVar>(_sv.v());
            _result = bexp::bvar(f(v_0));
          } else {
            const auto &[b0, body0] = std::get<typename bexp::BLet>(_sv.v());
            const auto &_sv0 = *b0;
            const auto &[v_00, def0] = _sv0;
            _stack.emplace_back(
                _after_map_bvars_in_Bind{crane_raw(body0), v_00});
            _stack.emplace_back(_call{&def0});
          }
        } else if (std::holds_alternative<_after_map_bvars_in_Bind>(_popped)) {
          auto _f = std::move(std::get<_after_map_bvars_in_Bind>(_popped));
          _stack.pop_back();
          const bexp &body0 = *_f.body0;
          uint64_t v_00 = _f.v_00;
          _stack.emplace_back(
              _after_map_bvars_in_Bind_2{v_00, std::move(_result)});
          _stack.emplace_back(_call{_f.body0});
        } else {
          auto _f = std::move(std::get<_after_map_bvars_in_Bind_2>(_popped));
          _stack.pop_back();
          uint64_t v_00 = _f.v_00;
          _result =
              bexp::blet(binding<bexp>::bind(f(v_00), std::move(_f._tmp2)),
                         std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
    T1 bexp_rec(F0 &&f, F1 &&f0) const {
      return this->template bexp_rect<T1>(f, f0);
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
    T1 bexp_rect(F0 &&f, F1 &&f0) const {
      const bexp *_self = this;

      // Explicit stack replaces the non-tail recursion of bexp_rect: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const bexp *_self;
      };

      struct _after_bexp_rect_in_BLet {
        std::shared_ptr<binding<bexp>> b1;
        std::shared_ptr<bexp> body0;
      };

      using _frame = std::variant<_call, _after_bexp_rect_in_BLet>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const bexp *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename bexp::BVar>(_sv.v())) {
            const auto &[v_0] = std::get<typename bexp::BVar>(_sv.v());
            _result = f(v_0);
          } else {
            const auto &[b1, body0] = std::get<typename bexp::BLet>(_sv.v());
            _stack.emplace_back(_after_bexp_rect_in_BLet{b1, body0});
            _stack.emplace_back(_call{crane_raw(body0)});
          }
        } else {
          auto _f = std::move(std::get<_after_bexp_rect_in_BLet>(_popped));
          _stack.pop_back();
          std::shared_ptr<binding<bexp>> b1 = std::move(_f.b1);
          std::shared_ptr<bexp> body0 = std::move(_f.body0);
          _result = f0(*b1, *body0, std::move(_result));
        }
      }
      return _result;
    }
  };

  /// Two recursive calls directly in one constructor.
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<tree> l;
      uint64_t x;
      std::shared_ptr<tree> r;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Leaf _v) : v_(_v) {}

    explicit tree(Node _v) : v_(std::move(_v)) {}

    static tree leaf() { return tree(Leaf{}); }

    static tree node(tree l, uint64_t x, tree r) {
      return tree(Node{std::make_shared<tree>(std::move(l)), x,
                       std::make_shared<tree>(std::move(r))});
    }

    // MANIPULATORS
    ~tree() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<Leaf>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<Node>(&v_mut())) {
        if (!((_alt->l && _alt->l.use_count() == 1) ||
              (_alt->r && _alt->r.use_count() == 1))) {
          return;
        }
      }
      crane::small_vector<std::shared_ptr<tree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->l && _alt->l.use_count() == 1) {
            _stack.push_back(std::move(_alt->l));
          }
          if (_alt->r && _alt->r.use_count() == 1) {
            _stack.push_back(std::move(_alt->r));
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

    tree(const tree &) = default;
    tree &operator=(const tree &) = default;
    tree(tree &&) = default;
    tree &operator=(tree &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename F0>
      requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
    tree map_tree(F0 &&f) const {
      const tree *_self = this;

      // Explicit stack replaces the non-tail recursion of map_tree: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const tree *_self;
      };

      struct _after_map_tree_in_Node {
        uint64_t x0;
        const tree *r0;
      };

      struct _after_map_tree_in_Node_2 {
        uint64_t x0;
        tree _tmp2;
      };

      using _frame = std::variant<_call, _after_map_tree_in_Node,
                                  _after_map_tree_in_Node_2>;
      tree _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = tree::leaf();
          } else {
            const auto &[l0, x0, r0] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_after_map_tree_in_Node{x0, crane_raw(r0)});
            _stack.emplace_back(_call{crane_raw(l0)});
          }
        } else if (std::holds_alternative<_after_map_tree_in_Node>(_popped)) {
          auto _f = std::move(std::get<_after_map_tree_in_Node>(_popped));
          _stack.pop_back();
          uint64_t x0 = _f.x0;
          const tree &r0 = *_f.r0;
          _stack.emplace_back(_after_map_tree_in_Node_2{x0,
                                                        std::move(_result)});
          _stack.emplace_back(_call{_f.r0});
        } else {
          auto _f = std::move(std::get<_after_map_tree_in_Node_2>(_popped));
          _stack.pop_back();
          uint64_t x0 = _f.x0;
          _result = tree::node(std::move(_f._tmp2), f(x0), std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1> T1 tree_rec(T1 f, F1 &&f0) const {
      return this->template tree_rect<T1>(std::move(f), f0);
    }

    template <typename T1, typename F1> T1 tree_rect(T1 f, F1 &&f0) const {
      const tree *_self = this;

      // Explicit stack replaces the non-tail recursion of tree_rect: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const tree *_self;
      };

      struct _after_tree_rect_in_Node {
        std::shared_ptr<tree> l0;
        uint64_t x0;
        const tree *r0;
      };

      struct _after_tree_rect_in_Node_2 {
        std::shared_ptr<tree> l0;
        uint64_t x0;
        const tree *r0;
        T1 _tmp2;
      };

      using _frame = std::variant<_call, _after_tree_rect_in_Node,
                                  _after_tree_rect_in_Node_2>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[l0, x0, r0] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_after_tree_rect_in_Node{l0, x0,
                                                         crane_raw(r0)});
            _stack.emplace_back(_call{crane_raw(l0)});
          }
        } else if (std::holds_alternative<_after_tree_rect_in_Node>(_popped)) {
          auto _f = std::move(std::get<_after_tree_rect_in_Node>(_popped));
          _stack.pop_back();
          std::shared_ptr<tree> l0 = std::move(_f.l0);
          uint64_t x0 = _f.x0;
          const tree &r0 = *_f.r0;
          _stack.emplace_back(_after_tree_rect_in_Node_2{std::move(l0), x0, &r0,
                                                         std::move(_result)});
          _stack.emplace_back(_call{_f.r0});
        } else {
          auto _f = std::move(std::get<_after_tree_rect_in_Node_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<tree> l0 = std::move(_f.l0);
          uint64_t x0 = _f.x0;
          const tree &r0 = *_f.r0;
          _result = f0(*l0, std::move(_f._tmp2), x0, r0, std::move(_result));
        }
      }
      return _result;
    }
  };

  /// One branch that tail modulo cons could take alone, one with two calls.
  struct term {
    // TYPES
    struct Lit {
      uint64_t n;
    };

    struct Neg {
      std::shared_ptr<term> t;
    };

    struct Add {
      std::shared_ptr<term> a;
      std::shared_ptr<term> b;
    };

    using variant_t = std::variant<Lit, Neg, Add>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    term() {}

    explicit term(Lit _v) : v_(std::move(_v)) {}

    explicit term(Neg _v) : v_(std::move(_v)) {}

    explicit term(Add _v) : v_(std::move(_v)) {}

    static term lit(uint64_t n) { return term(Lit{n}); }

    static term neg(term t) {
      return term(Neg{std::make_shared<term>(std::move(t))});
    }

    static term add(term a, term b) {
      return term(Add{std::make_shared<term>(std::move(a)),
                      std::make_shared<term>(std::move(b))});
    }

    // MANIPULATORS
    ~term() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<Lit>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<Neg>(&v_mut())) {
        if (!(_alt->t && _alt->t.use_count() == 1)) {
          return;
        }
      }
      if (auto *_alt = std::get_if<Add>(&v_mut())) {
        if (!((_alt->a && _alt->a.use_count() == 1) ||
              (_alt->b && _alt->b.use_count() == 1))) {
          return;
        }
      }
      crane::small_vector<std::shared_ptr<term>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Neg>(&_v)) {
          if (_alt->t && _alt->t.use_count() == 1) {
            _stack.push_back(std::move(_alt->t));
          }
        }
        if (auto *_alt = std::get_if<Add>(&_v)) {
          if (_alt->a && _alt->a.use_count() == 1) {
            _stack.push_back(std::move(_alt->a));
          }
          if (_alt->b && _alt->b.use_count() == 1) {
            _stack.push_back(std::move(_alt->b));
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

    term(const term &) = default;
    term &operator=(const term &) = default;
    term(term &&) = default;
    term &operator=(term &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t eval() const {
      const term *_self = this;

      // Explicit stack replaces the non-tail recursion of eval: _call frames
      // are pending calls, _after frames resume a caller.
      struct _call {
        const term *_self;
      };

      struct _after_eval_in_Add {
        const term *b0;
      };

      struct _after_eval_in_Add_2 {
        uint64_t _tmp2;
      };

      using _frame =
          std::variant<_call, _after_eval_in_Add, _after_eval_in_Add_2>;
      uint64_t _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const term *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename term::Lit>(_sv.v())) {
            const auto &[n0] = std::get<typename term::Lit>(_sv.v());
            _result = std::move(n0);
          } else if (std::holds_alternative<typename term::Neg>(_sv.v())) {
            const auto &[t1] = std::get<typename term::Neg>(_sv.v());
            _stack.emplace_back(_call{crane_raw(t1)});
          } else {
            const auto &[a0, b0] = std::get<typename term::Add>(_sv.v());
            _stack.emplace_back(_after_eval_in_Add{crane_raw(b0)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_eval_in_Add>(_popped)) {
          auto _f = std::move(std::get<_after_eval_in_Add>(_popped));
          _stack.pop_back();
          const term &b0 = *_f.b0;
          _stack.emplace_back(_after_eval_in_Add_2{std::move(_result)});
          _stack.emplace_back(_call{_f.b0});
        } else {
          auto _f = std::move(std::get<_after_eval_in_Add_2>(_popped));
          _stack.pop_back();
          _result = (_f._tmp2 + std::move(_result));
        }
      }
      return _result;
    }

    term scale(uint64_t k) const {
      const term *_self = this;

      // Explicit stack replaces the non-tail recursion of scale: _call frames
      // are pending calls, _after frames resume a caller.
      struct _call {
        const term *_self;
      };

      struct _after_scale_in_Add {
        const term *b0;
      };

      struct _after_scale_in_Add_2 {
        term _tmp3;
      };

      struct _after_scale_in_Neg {};

      using _frame = std::variant<_call, _after_scale_in_Add,
                                  _after_scale_in_Add_2, _after_scale_in_Neg>;
      term _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const term *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename term::Lit>(_sv.v())) {
            const auto &[n0] = std::get<typename term::Lit>(_sv.v());
            _result = term::lit((k * n0));
          } else if (std::holds_alternative<typename term::Neg>(_sv.v())) {
            const auto &[t1] = std::get<typename term::Neg>(_sv.v());
            _stack.emplace_back(_after_scale_in_Neg{});
            _stack.emplace_back(_call{crane_raw(t1)});
          } else {
            const auto &[a0, b0] = std::get<typename term::Add>(_sv.v());
            _stack.emplace_back(_after_scale_in_Add{crane_raw(b0)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_scale_in_Add>(_popped)) {
          auto _f = std::move(std::get<_after_scale_in_Add>(_popped));
          _stack.pop_back();
          const term &b0 = *_f.b0;
          _stack.emplace_back(_after_scale_in_Add_2{std::move(_result)});
          _stack.emplace_back(_call{_f.b0});
        } else if (std::holds_alternative<_after_scale_in_Add_2>(_popped)) {
          auto _f = std::move(std::get<_after_scale_in_Add_2>(_popped));
          _stack.pop_back();
          _result = term::add(std::move(_f._tmp3), std::move(_result));
        } else {
          auto _f = std::move(std::get<_after_scale_in_Neg>(_popped));
          _stack.pop_back();
          _result = term::neg(std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1, typename F2>
    T1 term_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      return this->template term_rect<T1>(f, f0, f1);
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
    T1 term_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      const term *_self = this;

      // Explicit stack replaces the non-tail recursion of term_rect: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const term *_self;
      };

      struct _after_term_rect_in_Add {
        std::shared_ptr<term> a0;
        const term *b0;
      };

      struct _after_term_rect_in_Add_2 {
        std::shared_ptr<term> a0;
        const term *b0;
        T1 _tmp3;
      };

      struct _after_term_rect_in_Neg {
        std::shared_ptr<term> t1;
      };

      using _frame =
          std::variant<_call, _after_term_rect_in_Add,
                       _after_term_rect_in_Add_2, _after_term_rect_in_Neg>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const term *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename term::Lit>(_sv.v())) {
            const auto &[n0] = std::get<typename term::Lit>(_sv.v());
            _result = f(n0);
          } else if (std::holds_alternative<typename term::Neg>(_sv.v())) {
            const auto &[t1] = std::get<typename term::Neg>(_sv.v());
            _stack.emplace_back(_after_term_rect_in_Neg{t1});
            _stack.emplace_back(_call{crane_raw(t1)});
          } else {
            const auto &[a0, b0] = std::get<typename term::Add>(_sv.v());
            _stack.emplace_back(_after_term_rect_in_Add{a0, crane_raw(b0)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_term_rect_in_Add>(_popped)) {
          auto _f = std::move(std::get<_after_term_rect_in_Add>(_popped));
          _stack.pop_back();
          std::shared_ptr<term> a0 = std::move(_f.a0);
          const term &b0 = *_f.b0;
          _stack.emplace_back(
              _after_term_rect_in_Add_2{std::move(a0), &b0,
                                        std::move(_result)});
          _stack.emplace_back(_call{_f.b0});
        } else if (std::holds_alternative<_after_term_rect_in_Add_2>(_popped)) {
          auto _f = std::move(std::get<_after_term_rect_in_Add_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<term> a0 = std::move(_f.a0);
          const term &b0 = *_f.b0;
          _result = f1(*a0, std::move(_f._tmp3), b0, std::move(_result));
        } else {
          auto _f = std::move(std::get<_after_term_rect_in_Neg>(_popped));
          _stack.pop_back();
          std::shared_ptr<term> t1 = std::move(_f.t1);
          _result = f0(*t1, std::move(_result));
        }
      }
      return _result;
    }
  };
};

#endif // INCLUDED_TMC_AMBIGUOUS_CALLS
