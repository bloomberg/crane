#ifndef INCLUDED_LOOPIFY_FILTER_FN_REF
#define INCLUDED_LOOPIFY_FILTER_FN_REF

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

struct LoopifyFilterFnRef {
  /// A binary tree with elements at nodes.
  template <typename A> struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<tree<A>> a0;
      A a1;
      std::shared_ptr<tree<A>> a2;
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

    template <typename CraneU>
    tree(const tree<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename tree<CraneU>::Leaf>(
                    _other.v())) {
              return Leaf{};
            } else {
              const auto &[a0, a1, a2] =
                  std::get<typename tree<CraneU>::Node>(_other.v());
              return Node{
                  (a0 ? std::make_shared<tree<A>>(crane_convert<tree<A>>(*a0))
                      : nullptr),
                  [&]() -> A {
                    if constexpr (crane_convertible<A, const CraneU &>) {
                      return crane_convert<A>(a1);
                    } else {
                      throw std::logic_error(
                          "unreachable: inactive constructor field at this "
                          "instantiation");
                    }
                  }(),
                  (a2 ? std::make_shared<tree<A>>(crane_convert<tree<A>>(*a2))
                      : nullptr)};
            }
          }()) {}

    static tree<A> leaf() { return tree<A>(Leaf{}); }

    static tree<A> node(tree<A> a0, A a1, tree<A> a2) {
      return tree<A>(Node{std::make_shared<tree<A>>(std::move(a0)),
                          std::move(a1),
                          std::make_shared<tree<A>>(std::move(a2))});
    }

    // MANIPULATORS
    ~tree() {
      crane::small_vector<std::shared_ptr<tree<A>>> _stack = {};
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
  };

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, tree<T1> &, T2 &, T1 &, tree<T1> &,
                                   T2 &>
  static T2
  tree_rect(T2 f, F1 &&f0,
            const tree<T1> &t) { /// CraneEnter: captures varying parameters for
                                 /// each recursive call.

    struct CraneEnter {
      const tree<T1> *t;
    };

    /// CraneCont_Node: saves [a0, a1, a2], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Node {
      std::shared_ptr<tree<T1>> a0;
      T1 a1;
      const tree<T1> *a2;
    };

    /// CraneCont_Node_1: saves [_tmp2, a0, a1, a2], resumes after recursive
    /// call, then processes rest.
    struct CraneCont_Node_1 {
      T2 _tmp2;
      std::shared_ptr<tree<T1>> a0;
      T1 a1;
      const tree<T1> *a2;
    };

    using CraneFrame =
        std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
    T2 _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&t});
    /// Loopified tree_rect: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const tree<T1> &t = *_f.t;
        if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
          _result = f;
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree<T1>::Node>(t.v());
          _stack.emplace_back(CraneCont_Node{a0, a1, crane_raw(a2)});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        }
      } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
        auto _f = std::move(std::get<CraneCont_Node>(_frame));
        std::shared_ptr<tree<T1>> a0 = std::move(_f.a0);
        auto a1 = std::move(_f.a1);
        const tree<T1> &a2 = *_f.a2;
        _stack.emplace_back(
            CraneCont_Node_1{std::move(_result), std::move(a0), a1, &a2});
        _stack.emplace_back(CraneEnter{&a2});
      } else {
        auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
        std::shared_ptr<tree<T1>> a0 = std::move(_f.a0);
        auto a1 = std::move(_f.a1);
        const tree<T1> &a2 = *_f.a2;
        _result = f0(*a0, std::move(_f._tmp2), a1, a2, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, tree<T1> &, T2 &, T1 &, tree<T1> &,
                                   T2 &>
  static T2
  tree_rec(T2 f, F1 &&f0,
           const tree<T1> &t) { /// CraneEnter: captures varying parameters for
                                /// each recursive call.

    struct CraneEnter {
      const tree<T1> *t;
    };

    /// CraneCont_Node: saves [a0, a1, a2], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Node {
      std::shared_ptr<tree<T1>> a0;
      T1 a1;
      const tree<T1> *a2;
    };

    /// CraneCont_Node_1: saves [_tmp2, a0, a1, a2], resumes after recursive
    /// call, then processes rest.
    struct CraneCont_Node_1 {
      T2 _tmp2;
      std::shared_ptr<tree<T1>> a0;
      T1 a1;
      const tree<T1> *a2;
    };

    using CraneFrame =
        std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
    T2 _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&t});
    /// Loopified tree_rec: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const tree<T1> &t = *_f.t;
        if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
          _result = f;
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree<T1>::Node>(t.v());
          _stack.emplace_back(CraneCont_Node{a0, a1, crane_raw(a2)});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        }
      } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
        auto _f = std::move(std::get<CraneCont_Node>(_frame));
        std::shared_ptr<tree<T1>> a0 = std::move(_f.a0);
        auto a1 = std::move(_f.a1);
        const tree<T1> &a2 = *_f.a2;
        _stack.emplace_back(
            CraneCont_Node_1{std::move(_result), std::move(a0), a1, &a2});
        _stack.emplace_back(CraneEnter{&a2});
      } else {
        auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
        std::shared_ptr<tree<T1>> a0 = std::move(_f.a0);
        auto a1 = std::move(_f.a1);
        const tree<T1> &a2 = *_f.a2;
        _result = f0(*a0, std::move(_f._tmp2), a1, a2, std::move(_result));
      }
    }
    return _result;
  }

  /// Recursive filter: takes a predicate f and recurses on both subtrees.
  /// When loopified, f is stored in continuation frame structs.
  /// If f is passed as a function reference (e.g. a named function),
  /// the template parameter F0 deduces to a reference type, and the
  /// generated frame struct field F0 f becomes ill-formed with std::move.
  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &>
  static tree<T1>
  filter(F0 &&f, const tree<T1> &t) { /// CraneEnter: captures varying
                                      /// parameters for each recursive call.

    struct CraneEnter {
      const tree<T1> *t;
    };

    /// CraneCont_Node: saves [a1, a2], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Node {
      T1 a1;
      const tree<T1> *a2;
    };

    /// CraneCont_Node_1: saves [a1, l_], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Node_1 {
      T1 a1;
      tree<T1> l_;
    };

    using CraneFrame =
        std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
    tree<T1> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&t});
    /// Loopified filter: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const tree<T1> &t = *_f.t;
        if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
          _result = tree<T1>::leaf();
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree<T1>::Node>(t.v());
          _stack.emplace_back(CraneCont_Node{a1, crane_raw(a2)});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        }
      } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
        auto _f = std::move(std::get<CraneCont_Node>(_frame));
        auto a1 = std::move(_f.a1);
        const tree<T1> &a2 = *_f.a2;
        tree<T1> l_ = std::move(_result);
        _stack.emplace_back(CraneCont_Node_1{a1, std::move(l_)});
        _stack.emplace_back(CraneEnter{&a2});
      } else {
        auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
        auto a1 = std::move(_f.a1);
        tree<T1> l_ = std::move(_f.l_);
        tree<T1> r_ = std::move(_result);
        if (f(a1)) {
          _result = tree<T1>::node(std::move(l_), a1, std::move(r_));
        } else {
          _result = std::move(l_);
        }
      }
    }
    return _result;
  }

  /// A concrete predicate — will be passed as a function reference.
  static bool is_positive(uint64_t n);
  /// Entry point that calls filter with a named function.
  static inline const tree<uint64_t> test_filter = filter<uint64_t>(
      is_positive, tree<uint64_t>::node(
                       tree<uint64_t>::node(tree<uint64_t>::leaf(), UINT64_C(0),
                                            tree<uint64_t>::leaf()),
                       UINT64_C(1),
                       tree<uint64_t>::node(tree<uint64_t>::leaf(), UINT64_C(2),
                                            tree<uint64_t>::leaf())));
};

#endif // INCLUDED_LOOPIFY_FILTER_FN_REF
