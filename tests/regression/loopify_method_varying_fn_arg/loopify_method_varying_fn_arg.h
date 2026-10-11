#ifndef INCLUDED_LOOPIFY_METHOD_VARYING_FN_ARG
#define INCLUDED_LOOPIFY_METHOD_VARYING_FN_ARG

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct LoopifyMethodVaryingFnArg {
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<tree> a0;
      uint64_t a1;
      std::shared_ptr<tree> a2;
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

    static tree node(tree a0, uint64_t a1, tree a2) {
      return tree(Node{std::make_shared<tree>(std::move(a0)), a1,
                       std::make_shared<tree>(std::move(a2))});
    }

    // MANIPULATORS
    ~tree() {
      if (std::holds_alternative<Leaf>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<Node>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a2 && _alt->a2.use_count() == 1))) {
          return;
        }
      }
      crane::small_vector<std::shared_ptr<tree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a2 && _alt->a2.use_count() == 1) {
            _stack.push_back(std::move(_alt->a2));
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

    uint64_t go(const crane::fn<uint64_t(uint64_t)> &f) const {
      const tree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const tree *_self;
        crane::fn<uint64_t(uint64_t)> f;
      };

      /// CraneCont_Node: saves [f, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Node {
        crane::fn<uint64_t(uint64_t)> f;
        const tree *a2;
      };

      /// CraneCont_Node_1: saves [_tmp2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Node_1 {
        uint64_t _tmp2;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self, f});
      /// Loopified go: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const tree *_self = _f._self;
          const crane::fn<uint64_t(uint64_t)> &f = std::move(_f.f);
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = f(UINT64_C(0));
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            const tree &a0_value = *a0;
            const tree &a2_value = *a2;
            _stack.emplace_back(CraneCont_Node{f, crane_raw(a2)});
            _stack.emplace_back(
                CraneEnter{&a0_value, [=](uint64_t y) { return f((y + a1)); }});
          }
        } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Node>(_frame));
          const crane::fn<uint64_t(uint64_t)> &f = std::move(_f.f);
          const tree &a2 = *_f.a2;
          const tree &a2_value = a2;
          _stack.emplace_back(CraneCont_Node_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{&a2_value, f});
        } else {
          auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
          _result = (_f._tmp2 + std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1> T1 tree_rec(T1 f, F1 &&f0) const {
      return this->template tree_rect<T1>(std::move(f), f0);
    }

    template <typename T1, typename F1> T1 tree_rect(T1 f, F1 &&f0) const {
      const tree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const tree *_self;
      };

      /// CraneCont_Node: saves [a0, a1, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Node {
        std::shared_ptr<tree> a0;
        uint64_t a1;
        const tree *a2;
      };

      /// CraneCont_Node_1: saves [_tmp2, a0, a1, a2], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_Node_1 {
        T1 _tmp2;
        std::shared_ptr<tree> a0;
        uint64_t a1;
        const tree *a2;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified tree_rect: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
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
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(CraneCont_Node{a0, a1, crane_raw(a2)});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Node>(_frame));
          std::shared_ptr<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          const tree &a2 = *_f.a2;
          _stack.emplace_back(
              CraneCont_Node_1{std::move(_result), std::move(a0), a1, &a2});
          _stack.emplace_back(CraneEnter{_f.a2});
        } else {
          auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
          std::shared_ptr<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          const tree &a2 = *_f.a2;
          _result = f0(*a0, std::move(_f._tmp2), a1, a2, std::move(_result));
        }
      }
      return _result;
    }
  };

  template <typename A> struct tagged {
    // DATA
    A x;

    // ACCESSORS
    tagged<A> clone() const { return {x}; }

    template <typename CraneU> operator tagged<CraneU>() const {
      return {[&]() -> CraneU {
        if constexpr (crane_convertible<CraneU, const A &>) {
          return crane_convert<CraneU>(x);
        } else {
          throw std::logic_error(
              "unreachable: inactive constructor field at this instantiation");
        }
      }()};
    }

    // CREATORS
    static tagged<A> tag(A x) { return {std::move(x)}; }

    template <typename T1, typename F0>
    T1 tagged_rec(F0 &&f, const A &_x) const {
      return this->template tagged_rect<T1>(f, _x);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, const A &>
    T1 tagged_rect(F0 &&f, const A &) const {
      const auto &[x0] = *this;
      return f(x0);
    }
  };

  static inline const uint64_t result =
      tree::node(tree::node(tree::leaf(), UINT64_C(1), tree::leaf()),
                 UINT64_C(2), tree::leaf())
          .go([](uint64_t x) { return (x + 1); });
};

#endif // INCLUDED_LOOPIFY_METHOD_VARYING_FN_ARG
