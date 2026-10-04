#ifndef INCLUDED_MUTUAL_LOOPIFY_ACC
#define INCLUDED_MUTUAL_LOOPIFY_ACC

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct MutualLoopifyAcc {
  struct tree;
  struct forest;

  struct tree {
    // TYPES
    struct Leaf {
      uint64_t a0;
    };

    struct Node {
      std::shared_ptr<forest> a0;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Leaf _v) : v_(std::move(_v)) {}

    explicit tree(Node _v) : v_(std::move(_v)) {}

    static tree leaf(uint64_t a0) { return tree(Leaf{a0}); }

    static tree node(forest a0) {
      return tree(Node{std::make_shared<forest>(std::move(a0))});
    }

    // MANIPULATORS
    ~tree() {
      crane::small_vector<crane::obj> _stack = {};
      auto _drain_self = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
        }
      };
      _drain_self(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (auto *_sp = crane::any_cast<std::shared_ptr<tree>>(&_cur)) {
          if (*_sp && (*_sp).use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            _drain_self((*_sp)->v_mut());
          }
        } else {
          if (auto *_sp = crane::any_cast<std::shared_ptr<forest>>(&_cur)) {
            if (*_sp && (*_sp).use_count() == 1) {
              auto &_pv = (*_sp)->v_mut();
              if (auto *_alt = std::get_if<typename forest::Fcons>(&_pv)) {
                if (_alt->a0 && _alt->a0.use_count() == 1) {
                  _stack.push_back(std::move(_alt->a0));
                }
                if (_alt->a1 && _alt->a1.use_count() == 1) {
                  _stack.push_back(std::move(_alt->a1));
                }
              }
            }
          }
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
  };

  struct forest {
    // TYPES
    struct Fnil {};

    struct Fcons {
      std::shared_ptr<tree> a0;
      std::shared_ptr<forest> a1;
    };

    using variant_t = std::variant<Fnil, Fcons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    forest() {}

    explicit forest(Fnil _v) : v_(_v) {}

    explicit forest(Fcons _v) : v_(std::move(_v)) {}

    static forest fnil() { return forest(Fnil{}); }

    static forest fcons(tree a0, forest a1) {
      return forest(Fcons{std::make_shared<tree>(std::move(a0)),
                          std::make_shared<forest>(std::move(a1))});
    }

    // MANIPULATORS
    ~forest() {
      crane::small_vector<crane::obj> _stack = {};
      auto _drain_self = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Fcons>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
      };
      _drain_self(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (auto *_sp = crane::any_cast<std::shared_ptr<forest>>(&_cur)) {
          if (*_sp && (*_sp).use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            _drain_self((*_sp)->v_mut());
          }
        } else {
          if (auto *_sp = crane::any_cast<std::shared_ptr<tree>>(&_cur)) {
            if (*_sp && (*_sp).use_count() == 1) {
              auto &_pv = (*_sp)->v_mut();
              if (auto *_alt = std::get_if<typename tree::Node>(&_pv)) {
                if (_alt->a0 && _alt->a0.use_count() == 1) {
                  _stack.push_back(std::move(_alt->a0));
                }
              }
            }
          }
        }
      }
    }

    forest(const forest &) = default;
    forest &operator=(const forest &) = default;
    forest(forest &&) = default;
    forest &operator=(forest &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
  static T1 tree_rect(F0 &&f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      const auto &[a0] = std::get<typename tree::Leaf>(t.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename tree::Node>(t.v());
      return f0(*a0);
    }
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
  static T1 tree_rec(F0 &&f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      const auto &[a0] = std::get<typename tree::Leaf>(t.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename tree::Node>(t.v());
      return f0(*a0);
    }
  }

  template <typename T1, typename F1>
  static T1
  forest_rect(T1 f, F1 &&f0,
              const forest &f1) { /// CraneEnter: captures varying parameters
                                  /// for each recursive call.

    struct CraneEnter {
      const forest *f1;
    };

    /// CraneCont_Fcons: saves [a0, a1], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Fcons {
      std::shared_ptr<tree> a0;
      std::shared_ptr<forest> a1;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Fcons>;
    T1 _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&f1});
    /// Loopified forest_rect: CraneEnter -> CraneCont_Fcons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const forest &f1 = *_f.f1;
        if (std::holds_alternative<typename forest::Fnil>(f1.v())) {
          _result = f;
        } else {
          const auto &[a0, a1] = std::get<typename forest::Fcons>(f1.v());
          _stack.emplace_back(CraneCont_Fcons{a0, a1});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Fcons>(_frame));
        std::shared_ptr<tree> a0 = std::move(_f.a0);
        std::shared_ptr<forest> a1 = std::move(_f.a1);
        _result = f0(*a0, *a1, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename F1>
  static T1
  forest_rec(T1 f, F1 &&f0,
             const forest &f1) { /// CraneEnter: captures varying parameters for
                                 /// each recursive call.

    struct CraneEnter {
      const forest *f1;
    };

    /// CraneCont_Fcons: saves [a0, a1], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Fcons {
      std::shared_ptr<tree> a0;
      std::shared_ptr<forest> a1;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Fcons>;
    T1 _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&f1});
    /// Loopified forest_rec: CraneEnter -> CraneCont_Fcons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const forest &f1 = *_f.f1;
        if (std::holds_alternative<typename forest::Fnil>(f1.v())) {
          _result = f;
        } else {
          const auto &[a0, a1] = std::get<typename forest::Fcons>(f1.v());
          _stack.emplace_back(CraneCont_Fcons{a0, a1});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Fcons>(_frame));
        std::shared_ptr<tree> a0 = std::move(_f.a0);
        std::shared_ptr<forest> a1 = std::move(_f.a1);
        _result = f0(*a0, *a1, std::move(_result));
      }
    }
    return _result;
  }

  static uint64_t tsum(uint64_t acc, const tree &t);
  static uint64_t fsum(uint64_t acc, const forest &f);
  static tree chain(uint64_t n, tree acc);
  static uint64_t go(uint64_t n);
};

#endif // INCLUDED_MUTUAL_LOOPIFY_ACC
