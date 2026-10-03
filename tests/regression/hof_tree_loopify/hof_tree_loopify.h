#ifndef INCLUDED_HOF_TREE_LOOPIFY
#define INCLUDED_HOF_TREE_LOOPIFY

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct HofTreeLoopify {
  template <typename A> struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<tree<A>> l;
      A x;
      std::shared_ptr<tree<A>> r;
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

    template <typename _U>
    tree(const tree<_U> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename tree<_U>::Leaf>(_other.v())) {
              return Leaf{};
            } else {
              const auto &[l, x, r] =
                  std::get<typename tree<_U>::Node>(_other.v());
              return Node{
                  (l ? std::make_shared<tree<A>>(crane_convert<tree<A>>(*l))
                     : nullptr),
                  [&]() -> A {
                    if constexpr (crane_convertible<A, const _U &>) {
                      return crane_convert<A>(x);
                    } else {
                      throw std::logic_error(
                          "unreachable: inactive constructor field at this "
                          "instantiation");
                    }
                  }(),
                  (r ? std::make_shared<tree<A>>(crane_convert<tree<A>>(*r))
                     : nullptr)};
            }
          }()) {}

    static tree<A> leaf() { return tree<A>(Leaf{}); }

    static tree<A> node(tree<A> l, A x, tree<A> r) {
      return tree<A>(Node{std::make_shared<tree<A>>(std::move(l)), std::move(x),
                          std::make_shared<tree<A>>(std::move(r))});
    }

    // MANIPULATORS
    ~tree() {
      crane::small_vector<std::shared_ptr<tree<A>>> _stack = {};
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
    tree(tree &&) noexcept = default;
    tree &operator=(tree &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, tree<T1> &, T2 &, T1 &, tree<T1> &,
                                   T2 &>
  static T2
  tree_rect(T2 f, F1 &&f0,
            const tree<T1> &t) { /// _Enter: captures varying parameters for
                                 /// each recursive call.

    struct _Enter {
      const tree<T1> *t;
    };

    /// _Cont_Node: saves [a0, a1, a2], resumes after recursive call, then
    /// processes rest.
    struct _Cont_Node {
      std::shared_ptr<tree<T1>> a0;
      T1 a1;
      const tree<T1> *a2;
    };

    /// _Cont_Node_1: saves [a0, a1, a2, r_], resumes after recursive call, then
    /// processes rest.
    struct _Cont_Node_1 {
      std::shared_ptr<tree<T1>> a0;
      T1 a1;
      const tree<T1> *a2;
      T2 r_;
    };

    using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
    T2 _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&t});
    /// Loopified tree_rect: _Enter -> _Cont_Node -> _Cont_Node_1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const tree<T1> &t = *_f.t;
        if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
          _result = f;
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree<T1>::Node>(t.v());
          _stack.emplace_back(_Cont_Node{a0, a1, crane_raw(a2)});
          _stack.emplace_back(_Enter{crane_raw(a0)});
        }
      } else if (std::holds_alternative<_Cont_Node>(_frame)) {
        auto _f = std::move(std::get<_Cont_Node>(_frame));
        std::shared_ptr<tree<T1>> a0 = std::move(_f.a0);
        auto a1 = std::move(_f.a1);
        const tree<T1> &a2 = *_f.a2;
        T2 r_ = std::move(_result);
        _stack.emplace_back(
            _Cont_Node_1{std::move(a0), a1, &a2, std::move(r_)});
        _stack.emplace_back(_Enter{&a2});
      } else {
        auto _f = std::move(std::get<_Cont_Node_1>(_frame));
        std::shared_ptr<tree<T1>> a0 = std::move(_f.a0);
        auto a1 = std::move(_f.a1);
        const tree<T1> &a2 = *_f.a2;
        auto r_ = std::move(_f.r_);
        T2 r_0 = std::move(_result);
        _result = f0(*a0, std::move(r_), a1, a2, std::move(r_0));
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, tree<T1> &, T2 &, T1 &, tree<T1> &,
                                   T2 &>
  static T2
  tree_rec(T2 f, F1 &&f0,
           const tree<T1> &t) { /// _Enter: captures varying parameters for each
                                /// recursive call.

    struct _Enter {
      const tree<T1> *t;
    };

    /// _Cont_Node: saves [a0, a1, a2], resumes after recursive call, then
    /// processes rest.
    struct _Cont_Node {
      std::shared_ptr<tree<T1>> a0;
      T1 a1;
      const tree<T1> *a2;
    };

    /// _Cont_Node_1: saves [a0, a1, a2, r_], resumes after recursive call, then
    /// processes rest.
    struct _Cont_Node_1 {
      std::shared_ptr<tree<T1>> a0;
      T1 a1;
      const tree<T1> *a2;
      T2 r_;
    };

    using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
    T2 _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&t});
    /// Loopified tree_rec: _Enter -> _Cont_Node -> _Cont_Node_1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const tree<T1> &t = *_f.t;
        if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
          _result = f;
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree<T1>::Node>(t.v());
          _stack.emplace_back(_Cont_Node{a0, a1, crane_raw(a2)});
          _stack.emplace_back(_Enter{crane_raw(a0)});
        }
      } else if (std::holds_alternative<_Cont_Node>(_frame)) {
        auto _f = std::move(std::get<_Cont_Node>(_frame));
        std::shared_ptr<tree<T1>> a0 = std::move(_f.a0);
        auto a1 = std::move(_f.a1);
        const tree<T1> &a2 = *_f.a2;
        T2 r_ = std::move(_result);
        _stack.emplace_back(
            _Cont_Node_1{std::move(a0), a1, &a2, std::move(r_)});
        _stack.emplace_back(_Enter{&a2});
      } else {
        auto _f = std::move(std::get<_Cont_Node_1>(_frame));
        std::shared_ptr<tree<T1>> a0 = std::move(_f.a0);
        auto a1 = std::move(_f.a1);
        const tree<T1> &a2 = *_f.a2;
        auto r_ = std::move(_f.r_);
        T2 r_0 = std::move(_result);
        _result = f0(*a0, std::move(r_), a1, a2, std::move(r_0));
      }
    }
    return _result;
  }

  static tree<uint64_t> depth_tree(uint64_t n);

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static tree<T2>
  tree_map(F0 &&f, const tree<T1> &t) { /// _Enter: captures varying parameters
                                        /// for each recursive call.

    struct _Enter {
      const tree<T1> *t;
    };

    /// _Cont_Node: saves [a1, a2], resumes after recursive call, then processes
    /// rest.
    struct _Cont_Node {
      T1 a1;
      const tree<T1> *a2;
    };

    /// _Resume_Node: saves [a1, r_], resumes after recursive call with _result.
    struct _Resume_Node {
      T2 a1;
      tree<T2> r_;
    };

    using _Frame = std::variant<_Enter, _Cont_Node, _Resume_Node>;
    tree<T2> _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&t});
    /// Loopified tree_map: _Enter -> _Cont_Node -> _Resume_Node.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const tree<T1> &t = *_f.t;
        if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
          _result = tree<T2>::leaf();
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree<T1>::Node>(t.v());
          _stack.emplace_back(_Cont_Node{a1, crane_raw(a2)});
          _stack.emplace_back(_Enter{crane_raw(a0)});
        }
      } else if (std::holds_alternative<_Cont_Node>(_frame)) {
        auto _f = std::move(std::get<_Cont_Node>(_frame));
        auto a1 = std::move(_f.a1);
        const tree<T1> &a2 = *_f.a2;
        tree<T2> r_ = std::move(_result);
        _stack.emplace_back(_Resume_Node{f(a1), std::move(r_)});
        _stack.emplace_back(_Enter{&a2});
      } else {
        auto _f = std::move(std::get<_Resume_Node>(_frame));
        _result = tree<T2>::node(std::move(_f.r_), std::move(_f.a1),
                                 std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T2 &, T1 &, T2 &>
  static T2
  tree_fold(T2 base, F1 &&f,
            const tree<T1> &t) { /// _Enter: captures varying parameters for
                                 /// each recursive call.

    struct _Enter {
      const tree<T1> *t;
    };

    /// _Cont_Node: saves [a1, a2], resumes after recursive call, then processes
    /// rest.
    struct _Cont_Node {
      T1 a1;
      const tree<T1> *a2;
    };

    /// _Cont_Node_1: saves [a1, r_], resumes after recursive call, then
    /// processes rest.
    struct _Cont_Node_1 {
      T1 a1;
      T2 r_;
    };

    using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
    T2 _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&t});
    /// Loopified tree_fold: _Enter -> _Cont_Node -> _Cont_Node_1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const tree<T1> &t = *_f.t;
        if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
          _result = base;
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree<T1>::Node>(t.v());
          _stack.emplace_back(_Cont_Node{a1, crane_raw(a2)});
          _stack.emplace_back(_Enter{crane_raw(a0)});
        }
      } else if (std::holds_alternative<_Cont_Node>(_frame)) {
        auto _f = std::move(std::get<_Cont_Node>(_frame));
        auto a1 = std::move(_f.a1);
        const tree<T1> &a2 = *_f.a2;
        T2 r_ = std::move(_result);
        _stack.emplace_back(_Cont_Node_1{a1, std::move(r_)});
        _stack.emplace_back(_Enter{&a2});
      } else {
        auto _f = std::move(std::get<_Cont_Node_1>(_frame));
        auto a1 = std::move(_f.a1);
        auto r_ = std::move(_f.r_);
        T2 r_0 = std::move(_result);
        _result = f(std::move(r_), a1, std::move(r_0));
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, T1 &, T2 &>
  static tree<T3>
  tree_zip_with(F0 &&f, const tree<T1> &t1,
                const tree<T2> &t2) { /// _Enter: captures varying parameters
                                      /// for each recursive call.

    struct _Enter {
      const tree<T2> *t2;
      const tree<T1> *t1;
    };

    /// _Cont_Node: saves [a1, a10, a2, a20], resumes after recursive call, then
    /// processes rest.
    struct _Cont_Node {
      T1 a1;
      T2 a10;
      const tree<T1> *a2;
      const tree<T2> *a20;
    };

    /// _Resume_Node: saves [_s0, r_], resumes after recursive call with
    /// _result.
    struct _Resume_Node {
      T3 _s0;
      tree<T3> r_;
    };

    using _Frame = std::variant<_Enter, _Cont_Node, _Resume_Node>;
    tree<T3> _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&t2, &t1});
    /// Loopified tree_zip_with: _Enter -> _Cont_Node -> _Resume_Node.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const tree<T2> &t2 = *_f.t2;
        const tree<T1> &t1 = *_f.t1;
        if (std::holds_alternative<typename tree<T1>::Leaf>(t1.v())) {
          _result = tree<T3>::leaf();
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree<T1>::Node>(t1.v());
          if (std::holds_alternative<typename tree<T2>::Leaf>(t2.v())) {
            _result = tree<T3>::leaf();
          } else {
            const auto &[a00, a10, a20] =
                std::get<typename tree<T2>::Node>(t2.v());
            _stack.emplace_back(
                _Cont_Node{a1, a10, crane_raw(a2), crane_raw(a20)});
            _stack.emplace_back(_Enter{crane_raw(a00), crane_raw(a0)});
          }
        }
      } else if (std::holds_alternative<_Cont_Node>(_frame)) {
        auto _f = std::move(std::get<_Cont_Node>(_frame));
        auto a1 = std::move(_f.a1);
        auto a10 = std::move(_f.a10);
        const tree<T1> &a2 = *_f.a2;
        const tree<T2> &a20 = *_f.a20;
        tree<T3> r_ = std::move(_result);
        _stack.emplace_back(_Resume_Node{f(a1, a10), std::move(r_)});
        _stack.emplace_back(_Enter{&a20, &a2});
      } else {
        auto _f = std::move(std::get<_Resume_Node>(_frame));
        _result = tree<T3>::node(std::move(_f.r_), std::move(_f._s0),
                                 std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<std::pair<T3, T2>, F0 &, T3 &, T1 &>
  static std::pair<T3, tree<T2>>
  tree_map_accum(F0 &&f, const T3 &acc,
                 const tree<T1> &t) { /// _Enter: captures varying parameters
                                      /// for each recursive call.

    struct _Enter {
      const tree<T1> *t;
      T3 acc;
    };

    /// _Cont_Node: saves [a1, a2], resumes after recursive call, then processes
    /// rest.
    struct _Cont_Node {
      T1 a1;
      const tree<T1> *a2;
    };

    /// _Cont_acc2: saves [l_, x_], resumes after recursive call, then processes
    /// rest.
    struct _Cont_acc2 {
      tree<T2> l_;
      T2 x_;
    };

    using _Frame = std::variant<_Enter, _Cont_Node, _Cont_acc2>;
    std::pair<T3, tree<T2>> _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&t, acc});
    /// Loopified tree_map_accum: _Enter -> _Cont_Node -> _Cont_acc2.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const tree<T1> &t = *_f.t;
        const T3 acc = std::move(_f.acc);
        if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
          _result = std::make_pair(acc, tree<T2>::leaf());
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree<T1>::Node>(t.v());
          _stack.emplace_back(_Cont_Node{a1, crane_raw(a2)});
          _stack.emplace_back(_Enter{crane_raw(a0), acc});
        }
      } else if (std::holds_alternative<_Cont_Node>(_frame)) {
        auto _f = std::move(std::get<_Cont_Node>(_frame));
        auto a1 = std::move(_f.a1);
        const tree<T1> &a2 = *_f.a2;
        std::pair<T3, tree<T2>> r_ = std::move(_result);
        auto [acc1, l_] = std::move(r_);
        auto [acc2, x_] = f(acc1, a1);
        _stack.emplace_back(_Cont_acc2{l_, x_});
        _stack.emplace_back(_Enter{&a2, acc2});
      } else {
        auto _f = std::move(std::get<_Cont_acc2>(_frame));
        tree<T2> l_ = std::move(_f.l_);
        auto x_ = std::move(_f.x_);
        std::pair<T3, tree<T2>> r_0 = std::move(_result);
        auto [acc3, r_1] = std::move(r_0);
        _result = std::make_pair(
            acc3, tree<T2>::node(std::move(l_), x_, std::move(r_1)));
      }
    }
    return _result;
  }

  static inline const tree<uint64_t> small_tree = tree<uint64_t>::node(
      tree<uint64_t>::node(
          tree<uint64_t>::node(tree<uint64_t>::leaf(), UINT64_C(1),
                               tree<uint64_t>::leaf()),
          UINT64_C(2),
          tree<uint64_t>::node(tree<uint64_t>::leaf(), UINT64_C(3),
                               tree<uint64_t>::leaf())),
      UINT64_C(4),
      tree<uint64_t>::node(
          tree<uint64_t>::node(tree<uint64_t>::leaf(), UINT64_C(5),
                               tree<uint64_t>::leaf()),
          UINT64_C(6),
          tree<uint64_t>::node(tree<uint64_t>::leaf(), UINT64_C(7),
                               tree<uint64_t>::leaf())));
  static inline const tree<uint64_t> mapped = tree_map<uint64_t, uint64_t>(
      [](uint64_t x) { return (x * UINT64_C(2)); }, small_tree);
  static inline const uint64_t folded = tree_fold<uint64_t, uint64_t>(
      UINT64_C(0),
      [](uint64_t l, uint64_t x, uint64_t r) { return ((l + x) + r); },
      small_tree);
  static inline const tree<uint64_t> zipped =
      tree_zip_with<uint64_t, uint64_t, uint64_t>(
          [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); },
          small_tree, small_tree);
  static inline const std::pair<uint64_t, tree<uint64_t>> accum =
      tree_map_accum<uint64_t, uint64_t, uint64_t>(
          [](uint64_t s, uint64_t x) { return std::make_pair((s + x), s); },
          UINT64_C(0), small_tree);
  static inline const tree<uint64_t> deep = depth_tree(UINT64_C(50000));
};

#endif // INCLUDED_HOF_TREE_LOOPIFY
