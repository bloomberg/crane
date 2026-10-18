#ifndef INCLUDED_METHOD_RETURNS_FUNCTION_ALIAS
#define INCLUDED_METHOD_RETURNS_FUNCTION_ALIAS

#include "crane_fn.h"
#include "fn.h"
#include "small_vector.h"
#include <atomic>
#include <memory>
#include <utility>
#include <variant>

struct Nat;

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

  static Nat s(Nat a0) { return Nat(S{std::make_shared<Nat>(std::move(a0))}); }

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

  bool eqb(const Nat &m) const {
    const Nat *_loop_self = this;
    const Nat *_loop_m = &m;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        if (std::holds_alternative<typename Nat::O>(_loop_m->v())) {
          return true;
        } else {
          return false;
        }
      } else {
        const auto &[a0] = std::get<typename Nat::S>(_sv.v());
        if (std::holds_alternative<typename Nat::O>(_loop_m->v())) {
          return false;
        } else {
          const auto &[a00] = std::get<typename Nat::S>(_loop_m->v());
          _loop_self = crane_raw(a0);
          _loop_m = crane_raw(a00);
        }
      }
    }
  }
};

struct MethodReturnsFunctionAlias {
  template <typename a> using pred = crane::fn<bool(a)>;
  static pred<Nat> always(bool b);

  struct Holder {
    pred<Nat> run;
    Nat tag;

    pred<Nat> runner() const {
      Holder _self_val = *this;
      return [=, _self_val = std::move(_self_val)](const Nat &s) {
        return _self_val.run(s);
      };
    }
  };

  struct Tree {
    struct tree {
      // TYPES
      struct Leaf {};

      struct Node {
        std::shared_ptr<tree> l;
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

      static tree node(tree l, tree r) {
        return tree(Node{std::make_shared<tree>(std::move(l)),
                         std::make_shared<tree>(std::move(r))});
      }

      // MANIPULATORS
      ~tree() {
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

      template <typename T1, typename F1> T1 tree_rect(T1 f, F1 &&f0) const {
        const tree *_self = this;

        /// CraneEnter: captures varying parameters for each recursive call.
        struct CraneEnter {
          const tree *_self;
        };

        /// CraneCont_Node: saves [l0, r0], resumes after recursive call, then
        /// processes rest.
        struct CraneCont_Node {
          std::shared_ptr<tree> l0;
          const tree *r0;
        };

        /// CraneCont_Node_1: saves [_tmp2, l0, r0], resumes after recursive
        /// call, then processes rest.
        struct CraneCont_Node_1 {
          T1 _tmp2;
          std::shared_ptr<tree> l0;
          const tree *r0;
        };

        using CraneFrame =
            std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
        T1 _result{};
        crane::small_vector<CraneFrame> _stack;
        _stack.emplace_back(CraneEnter{_self});
        /// Loopified tree_rect: CraneEnter -> CraneCont_Node ->
        /// CraneCont_Node_1.
        while (!_stack.empty()) {
          CraneFrame _frame = std::move(_stack.back());
          _stack.pop_back();
          if (std::holds_alternative<CraneEnter>(_frame)) {
            auto _f = std::move(std::get<CraneEnter>(_frame));
            const tree *_self = _f._self;
            auto &&_sv = *_self;
            if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
              _result = f;
            } else {
              const auto &[l0, r0] = std::get<typename tree::Node>(_sv.v());
              _stack.emplace_back(CraneCont_Node{l0, crane_raw(r0)});
              _stack.emplace_back(CraneEnter{crane_raw(l0)});
            }
          } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
            auto _f = std::move(std::get<CraneCont_Node>(_frame));
            std::shared_ptr<tree> l0 = std::move(_f.l0);
            const tree &r0 = *_f.r0;
            _stack.emplace_back(
                CraneCont_Node_1{std::move(_result), std::move(l0), &r0});
            _stack.emplace_back(CraneEnter{_f.r0});
          } else {
            auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
            std::shared_ptr<tree> l0 = std::move(_f.l0);
            const tree &r0 = *_f.r0;
            _result = f0(*l0, std::move(_f._tmp2), r0, std::move(_result));
          }
        }
        return _result;
      }

      template <typename T1, typename F1> T1 tree_rec(T1 f, F1 &&f0) const {
        return this->template tree_rect<T1>(std::move(f), f0);
      }

      pred<Nat> is_leaf() const {
        tree _self_val = *this;
        return [=](Nat) -> bool {
          if (std::holds_alternative<typename tree::Leaf>(_self_val.v())) {
            return true;
          } else {
            return false;
          }
        };
      }
    };
  };

  static inline const bool t1 = always(true)(Nat::o());
  static inline const bool t2 =
      Holder{[](const Nat &n) { return n.eqb(Nat::o()); }, Nat::s(Nat::o())}
          .runner()(Nat::o());
  static inline const bool t3 = Tree::tree::leaf().is_leaf()(Nat::o());
  static inline const bool t4 =
      Tree::tree::node(Tree::tree::leaf(), Tree::tree::leaf())
          .is_leaf()(Nat::o());
};

#endif // INCLUDED_METHOD_RETURNS_FUNCTION_ALIAS
