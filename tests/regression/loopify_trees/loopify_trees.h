#ifndef INCLUDED_LOOPIFY_TREES
#define INCLUDED_LOOPIFY_TREES

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) = default;
  List &operator=(List &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  List<A> app(List<A> m) const {
    std::optional<List<A>> _root{};
    std::shared_ptr<List<A>> *_write = nullptr;
    const List<A> *_loop_self = this;
    List<A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = std::move(_loop_m);
        (_write ? *(*_write = std::make_shared<List<A>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell = typename List<A>::Cons(a0, nullptr);
        List<A> &_node =
            (_write ? *(*_write = std::make_shared<List<A>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<A>::Cons>(_node.v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }
};

/// Consolidated UNIQUE tree algorithms - domain-specific tree operations.
struct LoopifyTrees {
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

    template <typename CraneU>
    tree(const tree<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename tree<CraneU>::Leaf>(
                    _other.v())) {
              return Leaf{};
            } else {
              const auto &[l, x, r] =
                  std::get<typename tree<CraneU>::Node>(_other.v());
              return Node{
                  (l ? std::make_shared<tree<A>>(crane_convert<tree<A>>(*l))
                     : nullptr),
                  [&]() -> A {
                    if constexpr (crane_convertible<A, const CraneU &>) {
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
    tree(tree &&) = default;
    tree &operator=(tree &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// tree_map f t applies f to all values in tree.
    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &>
    tree<T1> tree_map(F0 &&f) const {
      const tree<A> *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const tree<A> *_self;
      };

      /// CraneCont_Node: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Node {
        A a1;
        std::shared_ptr<tree<A>> a2;
      };

      /// CraneCont_Node_1: saves [_tmp2, a1], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Node_1 {
        tree<T1> _tmp2;
        A a1;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
      tree<T1> _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified tree_map: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const tree<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
            _result = tree<T1>::leaf();
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename tree<A>::Node>(_sv.v());
            _stack.emplace_back(CraneCont_Node{a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Node>(_frame));
          auto a1 = std::move(_f.a1);
          std::shared_ptr<tree<A>> a2 = std::move(_f.a2);
          _stack.emplace_back(CraneCont_Node_1{std::move(_result), a1});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
          auto a1 = std::move(_f.a1);
          _result =
              tree<T1>::node(std::move(_f._tmp2), f(a1), std::move(_result));
        }
      }
      return _result;
    }

    /// mirror_equal t1 t2 checks if t1 and t2 are mirror images.
    bool mirror_equal(const tree<A> &t2) const {
      const tree<A> *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const tree<A> *_self;
        const tree<A> *t2;
      };

      /// CraneCont_Node: saves [a00, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Node {
        const tree<A> *a00;
        std::shared_ptr<tree<A>> a2;
      };

      /// CraneCont_Node_1: saves [_tmp2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Node_1 {
        bool _tmp2;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
      bool _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self, &t2});
      /// Loopified mirror_equal: CraneEnter -> CraneCont_Node ->
      /// CraneCont_Node_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const tree<A> *_self = _f._self;
          const tree<A> &t2 = *_f.t2;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
            if (std::holds_alternative<typename tree<A>::Leaf>(t2.v())) {
              _result = true;
            } else {
              _result = false;
            }
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename tree<A>::Node>(_sv.v());
            if (std::holds_alternative<typename tree<A>::Leaf>(t2.v())) {
              _result = false;
            } else {
              const auto &[a00, a10, a20] =
                  std::get<typename tree<A>::Node>(t2.v());
              _stack.emplace_back(CraneCont_Node{crane_raw(a00), a2});
              _stack.emplace_back(CraneEnter{crane_raw(a0), crane_raw(a20)});
            }
          }
        } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Node>(_frame));
          const tree<A> &a00 = *_f.a00;
          std::shared_ptr<tree<A>> a2 = std::move(_f.a2);
          _stack.emplace_back(CraneCont_Node_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a2), &a00});
        } else {
          auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
          _result = ((_f._tmp2 && std::move(_result)) && true);
        }
      }
      return _result;
    }

    /// tree_to_list inorder traversal.
    List<A> tree_to_list() const {
      const tree<A> *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const tree<A> *_self;
      };

      /// CraneCont_Node: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Node {
        A a1;
        std::shared_ptr<tree<A>> a2;
      };

      /// CraneCont_Node_1: saves [_tmp2, a1], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Node_1 {
        List<A> _tmp2;
        A a1;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
      List<A> _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified tree_to_list: CraneEnter -> CraneCont_Node ->
      /// CraneCont_Node_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const tree<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
            _result = List<A>::nil();
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename tree<A>::Node>(_sv.v());
            _stack.emplace_back(CraneCont_Node{a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Node>(_frame));
          auto a1 = std::move(_f.a1);
          std::shared_ptr<tree<A>> a2 = std::move(_f.a2);
          _stack.emplace_back(CraneCont_Node_1{std::move(_result), a1});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
          auto a1 = std::move(_f.a1);
          _result =
              std::move(_f._tmp2).app(List<A>::cons(a1, std::move(_result)));
        }
      }
      return _result;
    }

    /// count_leaves counts leaf nodes.
    uint64_t count_leaves() const {
      const tree<A> *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const tree<A> *_self;
      };

      /// CraneCont_Node: saves [a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Node {
        std::shared_ptr<tree<A>> a2;
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
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified count_leaves: CraneEnter -> CraneCont_Node ->
      /// CraneCont_Node_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const tree<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
            _result = UINT64_C(1);
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename tree<A>::Node>(_sv.v());
            _stack.emplace_back(CraneCont_Node{a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Node>(_frame));
          std::shared_ptr<tree<A>> a2 = std::move(_f.a2);
          _stack.emplace_back(CraneCont_Node_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
          _result = (_f._tmp2 + std::move(_result));
        }
      }
      return _result;
    }

    A rightmost(A default0) const {
      const tree<A> *_loop_self = this;
      while (true) {
        auto &&_sv = *_loop_self;
        if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
          return default0;
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree<A>::Node>(_sv.v());
          auto &&_sv = *a2;
          if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
            return a1;
          } else {
            _loop_self = crane_raw(a2);
          }
        }
      }
    }

    /// leftmost/rightmost finds edge values.
    A leftmost(A default0) const {
      const tree<A> *_loop_self = this;
      while (true) {
        auto &&_sv = *_loop_self;
        if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
          return default0;
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree<A>::Node>(_sv.v());
          auto &&_sv = *a0;
          if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
            return a1;
          } else {
            _loop_self = crane_raw(a0);
          }
        }
      }
    }

    /// same_shape tests structural equality.
    template <typename T1> bool same_shape(const tree<T1> &t2) const {
      const tree<A> *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const tree<A> *_self;
        const tree<T1> *t2;
      };

      /// CraneCont_Node: saves [a2, a20], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Node {
        std::shared_ptr<tree<A>> a2;
        const tree<T1> *a20;
      };

      using CraneFrame = std::variant<CraneEnter, CraneCont_Node>;
      bool _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self, &t2});
      /// Loopified same_shape: CraneEnter -> CraneCont_Node.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const tree<A> *_self = _f._self;
          const tree<T1> &t2 = *_f.t2;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
            if (std::holds_alternative<typename tree<T1>::Leaf>(t2.v())) {
              _result = true;
            } else {
              _result = false;
            }
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename tree<A>::Node>(_sv.v());
            if (std::holds_alternative<typename tree<T1>::Leaf>(t2.v())) {
              _result = false;
            } else {
              const auto &[a00, a10, a20] =
                  std::get<typename tree<T1>::Node>(t2.v());
              _stack.emplace_back(CraneCont_Node{a2, crane_raw(a20)});
              _stack.emplace_back(CraneEnter{crane_raw(a0), crane_raw(a00)});
            }
          }
        } else {
          auto _f = std::move(std::get<CraneCont_Node>(_frame));
          std::shared_ptr<tree<A>> a2 = std::move(_f.a2);
          const tree<T1> &a20 = *_f.a20;
          bool _tmp1 = std::move(_result);
          if (_tmp1) {
            _stack.emplace_back(CraneEnter{crane_raw(a2), &a20});
          } else {
            _result = false;
          }
        }
      }
      return _result;
    }

    tree<A> mirror() const {
      const tree<A> *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const tree<A> *_self;
      };

      /// CraneCont_Node: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Node {
        std::shared_ptr<tree<A>> a0;
        A a1;
      };

      /// CraneCont_Node_1: saves [_tmp2, a1], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Node_1 {
        tree<A> _tmp2;
        A a1;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
      tree<A> _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified mirror: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const tree<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
            _result = tree<A>::leaf();
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename tree<A>::Node>(_sv.v());
            _stack.emplace_back(CraneCont_Node{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a2)});
          }
        } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Node>(_frame));
          std::shared_ptr<tree<A>> a0 = std::move(_f.a0);
          auto a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_Node_1{std::move(_result), a1});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else {
          auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
          auto a1 = std::move(_f.a1);
          _result = tree<A>::node(std::move(_f._tmp2), a1, std::move(_result));
        }
      }
      return _result;
    }

    uint64_t tree_size() const {
      const tree<A> *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const tree<A> *_self;
      };

      /// CraneCont_Node: saves [a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Node {
        std::shared_ptr<tree<A>> a2;
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
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified tree_size: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const tree<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename tree<A>::Node>(_sv.v());
            _stack.emplace_back(CraneCont_Node{a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Node>(_frame));
          std::shared_ptr<tree<A>> a2 = std::move(_f.a2);
          _stack.emplace_back(CraneCont_Node_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
          _result = ((_f._tmp2 + std::move(_result)) + 1);
        }
      }
      return _result;
    }

    uint64_t tree_height() const {
      const tree<A> *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const tree<A> *_self;
      };

      /// CraneCont_Node: saves [a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Node {
        std::shared_ptr<tree<A>> a2;
      };

      /// CraneCont_Node_1: saves [lh], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Node_1 {
        uint64_t lh;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified tree_height: CraneEnter -> CraneCont_Node ->
      /// CraneCont_Node_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const tree<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename tree<A>::Node>(_sv.v());
            _stack.emplace_back(CraneCont_Node{a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Node>(_frame));
          std::shared_ptr<tree<A>> a2 = std::move(_f.a2);
          uint64_t lh = std::move(_result);
          _stack.emplace_back(CraneCont_Node_1{lh});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
          uint64_t lh = _f.lh;
          uint64_t rh = std::move(_result);
          _result = ((lh <= rh ? rh : lh) + 1);
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
    T1 tree_rec(const T1 &f, F1 &&f0) const {
      return this->template tree_rect<T1>(f, f0);
    }

    template <typename T1, typename F1> T1 tree_rect(T1 f, F1 &&f0) const {
      const tree<A> *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const tree<A> *_self;
      };

      /// CraneCont_Node: saves [a0, a1, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Node {
        std::shared_ptr<tree<A>> a0;
        A a1;
        std::shared_ptr<tree<A>> a2;
      };

      /// CraneCont_Node_1: saves [_tmp2, a0, a1, a2], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_Node_1 {
        T1 _tmp2;
        std::shared_ptr<tree<A>> a0;
        A a1;
        std::shared_ptr<tree<A>> a2;
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
          const tree<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename tree<A>::Node>(_sv.v());
            _stack.emplace_back(CraneCont_Node{a0, a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Node>(_frame));
          std::shared_ptr<tree<A>> a0 = std::move(_f.a0);
          auto a1 = std::move(_f.a1);
          std::shared_ptr<tree<A>> a2 = std::move(_f.a2);
          _stack.emplace_back(
              CraneCont_Node_1{std::move(_result), std::move(a0), a1, a2});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
          std::shared_ptr<tree<A>> a0 = std::move(_f.a0);
          auto a1 = std::move(_f.a1);
          std::shared_ptr<tree<A>> a2 = std::move(_f.a2);
          _result = f0(*a0, std::move(_f._tmp2), a1, *a2, std::move(_result));
        }
      }
      return _result;
    }
  };

  static uint64_t tree_sum(const tree<uint64_t> &t);
  /// leaf_sum sums only leaf values.
  static uint64_t leaf_sum(const tree<uint64_t> &t);
  /// insert_bst BST insertion.
  static tree<uint64_t> insert_bst(uint64_t x, const tree<uint64_t> &t);
  /// count_paths t n counts root-to-leaf paths that sum to n.
  static uint64_t count_paths(const tree<uint64_t> &t, uint64_t n);
  /// sum_of_max_branches sums maximum values along each path.
  static uint64_t sum_of_max_branches(const tree<uint64_t> &t);

  struct ternary {
    // TYPES
    struct TLeaf {};

    struct TNode {
      std::shared_ptr<ternary> a0;
      std::shared_ptr<ternary> a1;
      std::shared_ptr<ternary> a2;
      uint64_t a3;
    };

    using variant_t = std::variant<TLeaf, TNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    ternary() {}

    explicit ternary(TLeaf _v) : v_(_v) {}

    explicit ternary(TNode _v) : v_(std::move(_v)) {}

    static ternary tleaf() { return ternary(TLeaf{}); }

    static ternary tnode(ternary a0, ternary a1, ternary a2, uint64_t a3) {
      return ternary(TNode{std::make_shared<ternary>(std::move(a0)),
                           std::make_shared<ternary>(std::move(a1)),
                           std::make_shared<ternary>(std::move(a2)), a3});
    }

    // MANIPULATORS
    ~ternary() {
      crane::small_vector<std::shared_ptr<ternary>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<TNode>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            _stack.push_back(std::move(_alt->a1));
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

    ternary(const ternary &) = default;
    ternary &operator=(const ternary &) = default;
    ternary(ternary &&) = default;
    ternary &operator=(ternary &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t ternary_depth() const {
      const ternary *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const ternary *_self;
      };

      /// CraneCont_TNode: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_TNode {
        std::shared_ptr<ternary> a1;
        std::shared_ptr<ternary> a2;
      };

      /// CraneCont_TNode_1: saves [a2, d1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_TNode_1 {
        std::shared_ptr<ternary> a2;
        uint64_t d1;
      };

      /// CraneCont_TNode_2: saves [d1, d2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_TNode_2 {
        uint64_t d1;
        uint64_t d2;
      };

      using CraneFrame = std::variant<CraneEnter, CraneCont_TNode,
                                      CraneCont_TNode_1, CraneCont_TNode_2>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified ternary_depth: CraneEnter -> CraneCont_TNode ->
      /// CraneCont_TNode_1 -> CraneCont_TNode_2.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const ternary *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ternary::TLeaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename ternary::TNode>(_sv.v());
            _stack.emplace_back(CraneCont_TNode{a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_TNode>(_frame)) {
          auto _f = std::move(std::get<CraneCont_TNode>(_frame));
          std::shared_ptr<ternary> a1 = std::move(_f.a1);
          std::shared_ptr<ternary> a2 = std::move(_f.a2);
          uint64_t d1 = std::move(_result);
          _stack.emplace_back(CraneCont_TNode_1{std::move(a2), d1});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_TNode_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_TNode_1>(_frame));
          std::shared_ptr<ternary> a2 = std::move(_f.a2);
          uint64_t d1 = _f.d1;
          uint64_t d2 = std::move(_result);
          _stack.emplace_back(CraneCont_TNode_2{d1, d2});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<CraneCont_TNode_2>(_frame));
          uint64_t d1 = _f.d1;
          uint64_t d2 = _f.d2;
          uint64_t d3 = std::move(_result);
          _result = ([&]() -> uint64_t {
            if ((d1 <= d2 ? d2 : d1) <= d3) {
              return d3;
            } else {
              if (d1 <= d2) {
                return d2;
              } else {
                return d1;
              }
            }
          }() + 1);
        }
      }
      return _result;
    }

    uint64_t ternary_sum() const {
      const ternary *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const ternary *_self;
      };

      /// CraneCont_TNode: saves [a1, a2, a3], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_TNode {
        std::shared_ptr<ternary> a1;
        std::shared_ptr<ternary> a2;
        uint64_t a3;
      };

      /// CraneCont_TNode_1: saves [_tmp3, a2, a3], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_TNode_1 {
        uint64_t _tmp3;
        std::shared_ptr<ternary> a2;
        uint64_t a3;
      };

      /// CraneCont_TNode_2: saves [_tmp2, _tmp3, a3], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_TNode_2 {
        uint64_t _tmp2;
        uint64_t _tmp3;
        uint64_t a3;
      };

      using CraneFrame = std::variant<CraneEnter, CraneCont_TNode,
                                      CraneCont_TNode_1, CraneCont_TNode_2>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified ternary_sum: CraneEnter -> CraneCont_TNode ->
      /// CraneCont_TNode_1 -> CraneCont_TNode_2.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const ternary *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ternary::TLeaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename ternary::TNode>(_sv.v());
            _stack.emplace_back(CraneCont_TNode{a1, a2, a3});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_TNode>(_frame)) {
          auto _f = std::move(std::get<CraneCont_TNode>(_frame));
          std::shared_ptr<ternary> a1 = std::move(_f.a1);
          std::shared_ptr<ternary> a2 = std::move(_f.a2);
          uint64_t a3 = _f.a3;
          _stack.emplace_back(
              CraneCont_TNode_1{std::move(_result), std::move(a2), a3});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_TNode_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_TNode_1>(_frame));
          std::shared_ptr<ternary> a2 = std::move(_f.a2);
          uint64_t a3 = _f.a3;
          _stack.emplace_back(
              CraneCont_TNode_2{std::move(_result), _f._tmp3, a3});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<CraneCont_TNode_2>(_frame));
          uint64_t a3 = _f.a3;
          _result = (a3 + (_f._tmp3 + (_f._tmp2 + std::move(_result))));
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
    T1 ternary_rec(const T1 &f, F1 &&f0) const {
      return this->template ternary_rect<T1>(f, f0);
    }

    template <typename T1, typename F1> T1 ternary_rect(T1 f, F1 &&f0) const {
      const ternary *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const ternary *_self;
      };

      /// CraneCont_TNode: saves [a0, a1, a2, a3], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_TNode {
        std::shared_ptr<ternary> a0;
        std::shared_ptr<ternary> a1;
        std::shared_ptr<ternary> a2;
        uint64_t a3;
      };

      /// CraneCont_TNode_1: saves [_tmp3, a0, a1, a2, a3], resumes after
      /// recursive call, then processes rest.
      struct CraneCont_TNode_1 {
        T1 _tmp3;
        std::shared_ptr<ternary> a0;
        std::shared_ptr<ternary> a1;
        std::shared_ptr<ternary> a2;
        uint64_t a3;
      };

      /// CraneCont_TNode_2: saves [_tmp2, _tmp3, a0, a1, a2, a3], resumes after
      /// recursive call, then processes rest.
      struct CraneCont_TNode_2 {
        T1 _tmp2;
        T1 _tmp3;
        std::shared_ptr<ternary> a0;
        std::shared_ptr<ternary> a1;
        std::shared_ptr<ternary> a2;
        uint64_t a3;
      };

      using CraneFrame = std::variant<CraneEnter, CraneCont_TNode,
                                      CraneCont_TNode_1, CraneCont_TNode_2>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified ternary_rect: CraneEnter -> CraneCont_TNode ->
      /// CraneCont_TNode_1 -> CraneCont_TNode_2.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const ternary *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ternary::TLeaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename ternary::TNode>(_sv.v());
            _stack.emplace_back(CraneCont_TNode{a0, a1, a2, a3});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_TNode>(_frame)) {
          auto _f = std::move(std::get<CraneCont_TNode>(_frame));
          std::shared_ptr<ternary> a0 = std::move(_f.a0);
          std::shared_ptr<ternary> a1 = std::move(_f.a1);
          std::shared_ptr<ternary> a2 = std::move(_f.a2);
          uint64_t a3 = _f.a3;
          _stack.emplace_back(CraneCont_TNode_1{
              std::move(_result), std::move(a0), a1, std::move(a2), a3});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_TNode_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_TNode_1>(_frame));
          std::shared_ptr<ternary> a0 = std::move(_f.a0);
          std::shared_ptr<ternary> a1 = std::move(_f.a1);
          std::shared_ptr<ternary> a2 = std::move(_f.a2);
          uint64_t a3 = _f.a3;
          _stack.emplace_back(
              CraneCont_TNode_2{std::move(_result), std::move(_f._tmp3),
                                std::move(a0), std::move(a1), a2, a3});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<CraneCont_TNode_2>(_frame));
          std::shared_ptr<ternary> a0 = std::move(_f.a0);
          std::shared_ptr<ternary> a1 = std::move(_f.a1);
          std::shared_ptr<ternary> a2 = std::move(_f.a2);
          uint64_t a3 = _f.a3;
          _result = f0(*a0, std::move(_f._tmp3), *a1, std::move(_f._tmp2), *a2,
                       std::move(_result), a3);
        }
      }
      return _result;
    }
  };

  /// Rose tree: a tree with variable number of children.
  struct rose {
    // TYPES
    struct RNode {
      uint64_t a0;
      std::shared_ptr<List<rose>> a1;
    };

    using variant_t = std::variant<RNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    rose() {}

    explicit rose(RNode _v) : v_(std::move(_v)) {}

    static rose rnode(uint64_t a0, List<rose> a1) {
      return rose(RNode{a0, std::make_shared<List<rose>>(std::move(a1))});
    }

    // MANIPULATORS
    ~rose() {
      crane::small_vector<std::shared_ptr<rose>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<RNode>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            auto _lp = _alt->a1.get();
            while (
                std::holds_alternative<typename List<rose>::Cons>(_lp->v())) {
              auto &_lc = std::get<typename List<rose>::Cons>(_lp->v_mut());
              _stack.push_back(std::make_shared<rose>(std::move(_lc.a)));
              if (_lc.l && _lc.l.use_count() == 1) {
                std::atomic_thread_fence(std::memory_order_acquire);
                _lp = _lc.l.get();
              } else {
                break;
              }
            }
            _alt->a1.reset();
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

    rose(const rose &) = default;
    rose &operator=(const rose &) = default;
    rose(rose &&) = default;
    rose &operator=(rose &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// rose_depth t computes the depth of a rose tree.
    uint64_t rose_depth() const {
      const auto &[a0, a1] = std::get<typename rose::RNode>(this->v());
      return (depth_rose_list_fuel(UINT64_C(1000), *a1) + 1);
    }

    /// rose_flatten t flattens a rose tree to a list (pre-order).
    List<uint64_t> rose_flatten() const {
      const auto &[a0, a1] = std::get<typename rose::RNode>(this->v());
      return List<uint64_t>::cons(a0,
                                  flatten_rose_list_fuel(UINT64_C(1000), *a1));
    }

    /// rose_map f t applies f to all values in a rose tree.
    template <typename F0>
      requires std::is_invocable_r_v<uint64_t, F0 &, const uint64_t &>
    rose rose_map(F0 &&f) const {
      const auto &[a0, a1] = std::get<typename rose::RNode>(this->v());
      return rose::rnode(f(a0), map_rose_list_fuel(UINT64_C(1000), f, *a1));
    }

    /// rose_sum t sums all values in a rose tree.
    uint64_t rose_sum() const {
      const auto &[a0, a1] = std::get<typename rose::RNode>(this->v());
      return (a0 + sum_rose_list_fuel(UINT64_C(1000), *a1));
    }

    template <typename T1, typename F0> T1 rose_rec(F0 &&f) const {
      return this->template rose_rect<T1>(f);
    }

    template <typename T1, typename F0> T1 rose_rect(F0 &&f) const {
      const auto &[a0, a1] = std::get<typename rose::RNode>(this->v());
      return f(a0, *a1);
    }
  };

  /// Helper: sum all values in a list of rose trees (processes both tree and
  /// list levels in one recursive function to enable full loopification).
  static uint64_t sum_rose_list_fuel(uint64_t fuel, const List<rose> &cs);

  /// Helper: map function over all values in a list of rose trees.
  template <typename F1>
    requires std::is_invocable_r_v<uint64_t, F1 &, uint64_t &>
  static List<rose> map_rose_list_fuel(
      uint64_t fuel, F1 &&f,
      const List<rose> &cs) { /// CraneEnter: captures varying parameters for
                              /// each recursive call.

    struct CraneEnter {
      const List<rose> *cs;
      uint64_t fuel;
    };

    /// CraneCont_RNode: saves [a00, a1, g], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_RNode {
      uint64_t a00;
      const List<rose> *a1;
      uint64_t g;
    };

    /// CraneCont_RNode_1: saves [_tmp2, a00], resumes after recursive call,
    /// then processes rest.
    struct CraneCont_RNode_1 {
      List<rose> _tmp2;
      uint64_t a00;
    };

    using CraneFrame =
        std::variant<CraneEnter, CraneCont_RNode, CraneCont_RNode_1>;
    List<rose> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&cs, fuel});
    /// Loopified map_rose_list_fuel: CraneEnter -> CraneCont_RNode ->
    /// CraneCont_RNode_1.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<rose> &cs = *_f.cs;
        uint64_t fuel = _f.fuel;
        if (fuel <= 0) {
          _result = List<rose>::nil();
        } else {
          uint64_t g = fuel - 1;
          if (std::holds_alternative<typename List<rose>::Nil>(cs.v())) {
            _result = List<rose>::nil();
          } else {
            const auto &[a0, a1] = std::get<typename List<rose>::Cons>(cs.v());
            const auto &[a00, a10] = std::get<typename rose::RNode>(a0.v());
            _stack.emplace_back(CraneCont_RNode{a00, crane_raw(a1), g});
            _stack.emplace_back(CraneEnter{crane_raw(a10), g});
          }
        }
      } else if (std::holds_alternative<CraneCont_RNode>(_frame)) {
        auto _f = std::move(std::get<CraneCont_RNode>(_frame));
        uint64_t a00 = _f.a00;
        const List<rose> &a1 = *_f.a1;
        uint64_t g = _f.g;
        _stack.emplace_back(CraneCont_RNode_1{std::move(_result), a00});
        _stack.emplace_back(CraneEnter{&a1, g});
      } else {
        auto _f = std::move(std::get<CraneCont_RNode_1>(_frame));
        uint64_t a00 = _f.a00;
        _result = List<rose>::cons(rose::rnode(f(a00), std::move(_f._tmp2)),
                                   std::move(_result));
      }
    }
    return _result;
  }

  /// Helper: flatten a list of rose trees to a flat list of nats.
  static List<uint64_t> flatten_rose_list_fuel(uint64_t fuel,
                                               const List<rose> &cs);
  /// Helper: compute maximum depth among a list of rose trees.
  static uint64_t depth_rose_list_fuel(uint64_t fuel, const List<rose> &cs);
  /// tree_max t1 t2 element-wise maximum of two trees.
  static tree<uint64_t> tree_max(tree<uint64_t> t1, tree<uint64_t> t2);
  /// Helper: extract values from trees.
  static List<uint64_t> extract_tree_values(const List<tree<uint64_t>> &ts);
  /// Helper: extract children from trees.
  static List<tree<uint64_t>>
  extract_tree_children(const List<tree<uint64_t>> &ts);
  /// tree_levels t returns list of lists, one per level (breadth-first).
  static List<List<uint64_t>>
  tree_levels_fuel(uint64_t fuel, const List<tree<uint64_t>> &trees);
  static List<List<uint64_t>> tree_levels(const tree<uint64_t> &t);
  /// count_nodes t returns tuple (node_count, sum_of_values).
  static std::pair<uint64_t, uint64_t> count_nodes(const tree<uint64_t> &t);
  /// Helper: append two lists of lists.
  static List<List<uint64_t>> append_list_lists(const List<List<uint64_t>> &l1,
                                                List<List<uint64_t>> l2);
  /// Helper: prepend value to all lists in a list of lists.
  static List<List<uint64_t>> map_cons_to_all(uint64_t x,
                                              const List<List<uint64_t>> &lsts);
  /// paths t returns all root-to-leaf paths in tree.
  static List<List<uint64_t>> paths(const tree<uint64_t> &t);
  /// collect_sorted t collects and sorts all tree values.
  static List<uint64_t> collect_unsorted(const tree<uint64_t> &t);
  /// Simple insertion sort for collect_sorted.
  static List<uint64_t> insert_sorted(uint64_t x, const List<uint64_t> &l);
  static List<uint64_t> sort_list(const List<uint64_t> &l);
  static List<uint64_t> collect_sorted(const tree<uint64_t> &t);

  /// or_search p t searches tree for element satisfying predicate.
  template <typename F0>
  static bool
  or_search(F0 &&p,
            const tree<uint64_t> &t) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

    struct CraneEnter {
      const tree<uint64_t> *t;
    };

    /// CraneCont1: saves [a2], resumes after recursive call, then processes
    /// rest.
    struct CraneCont1 {
      const tree<uint64_t> *a2;
    };

    /// CraneCont2: saves [_tmp2], resumes after recursive call, then processes
    /// rest.
    struct CraneCont2 {
      bool _tmp2;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont1, CraneCont2>;
    bool _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&t});
    /// Loopified or_search: CraneEnter -> CraneCont1 -> CraneCont2.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const tree<uint64_t> &t = *_f.t;
        if (std::holds_alternative<typename tree<uint64_t>::Leaf>(t.v())) {
          _result = false;
        } else {
          const auto &[a0, a1, a2] =
              std::get<typename tree<uint64_t>::Node>(t.v());
          if (p(a1)) {
            _result = true;
          } else {
            _stack.emplace_back(CraneCont1{crane_raw(a2)});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        }
      } else if (std::holds_alternative<CraneCont1>(_frame)) {
        auto _f = std::move(std::get<CraneCont1>(_frame));
        const tree<uint64_t> &a2 = *_f.a2;
        _stack.emplace_back(CraneCont2{std::move(_result)});
        _stack.emplace_back(CraneEnter{&a2});
      } else {
        auto _f = std::move(std::get<CraneCont2>(_frame));
        _result = (_f._tmp2 || std::move(_result));
      }
    }
    return _result;
  }

  struct quadtree {
    // TYPES
    struct QLeaf {
      uint64_t a0;
    };

    struct Quad {
      std::shared_ptr<quadtree> a0;
      std::shared_ptr<quadtree> a1;
      std::shared_ptr<quadtree> a2;
      std::shared_ptr<quadtree> a3;
    };

    using variant_t = std::variant<QLeaf, Quad>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    quadtree() {}

    explicit quadtree(QLeaf _v) : v_(std::move(_v)) {}

    explicit quadtree(Quad _v) : v_(std::move(_v)) {}

    static quadtree qleaf(uint64_t a0) { return quadtree(QLeaf{a0}); }

    static quadtree quad(quadtree a0, quadtree a1, quadtree a2, quadtree a3) {
      return quadtree(Quad{std::make_shared<quadtree>(std::move(a0)),
                           std::make_shared<quadtree>(std::move(a1)),
                           std::make_shared<quadtree>(std::move(a2)),
                           std::make_shared<quadtree>(std::move(a3))});
    }

    // MANIPULATORS
    ~quadtree() {
      crane::small_vector<std::shared_ptr<quadtree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Quad>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
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

    quadtree(const quadtree &) = default;
    quadtree &operator=(const quadtree &) = default;
    quadtree(quadtree &&) = default;
    quadtree &operator=(quadtree &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// quad_depth t computes depth of quadtree.
    uint64_t quad_depth() const {
      const quadtree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const quadtree *_self;
      };

      /// CraneCont_Quad: saves [a1, a2, a3], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Quad {
        std::shared_ptr<quadtree> a1;
        std::shared_ptr<quadtree> a2;
        std::shared_ptr<quadtree> a3;
      };

      /// CraneCont_Quad_1: saves [_tmp4, a2, a3], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Quad_1 {
        uint64_t _tmp4;
        std::shared_ptr<quadtree> a2;
        std::shared_ptr<quadtree> a3;
      };

      /// CraneCont_Quad_2: saves [_tmp3, _tmp4, a3], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_Quad_2 {
        uint64_t _tmp3;
        uint64_t _tmp4;
        std::shared_ptr<quadtree> a3;
      };

      /// CraneCont_Quad_3: saves [_tmp2, _tmp3, _tmp4], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_Quad_3 {
        uint64_t _tmp2;
        uint64_t _tmp3;
        uint64_t _tmp4;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Quad, CraneCont_Quad_1,
                       CraneCont_Quad_2, CraneCont_Quad_3>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified quad_depth: CraneEnter -> CraneCont_Quad -> CraneCont_Quad_1
      /// -> CraneCont_Quad_2 -> CraneCont_Quad_3.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const quadtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename quadtree::Quad>(_sv.v());
            _stack.emplace_back(CraneCont_Quad{a1, a2, a3});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Quad>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Quad>(_frame));
          std::shared_ptr<quadtree> a1 = std::move(_f.a1);
          std::shared_ptr<quadtree> a2 = std::move(_f.a2);
          std::shared_ptr<quadtree> a3 = std::move(_f.a3);
          _stack.emplace_back(CraneCont_Quad_1{std::move(_result),
                                               std::move(a2), std::move(a3)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_Quad_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Quad_1>(_frame));
          std::shared_ptr<quadtree> a2 = std::move(_f.a2);
          std::shared_ptr<quadtree> a3 = std::move(_f.a3);
          _stack.emplace_back(
              CraneCont_Quad_2{std::move(_result), _f._tmp4, std::move(a3)});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else if (std::holds_alternative<CraneCont_Quad_2>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Quad_2>(_frame));
          std::shared_ptr<quadtree> a3 = std::move(_f.a3);
          _stack.emplace_back(
              CraneCont_Quad_3{std::move(_result), _f._tmp3, _f._tmp4});
          _stack.emplace_back(CraneEnter{crane_raw(a3)});
        } else {
          auto _f = std::move(std::get<CraneCont_Quad_3>(_frame));
          _result =
              (max4_impl(_f._tmp4, _f._tmp3, _f._tmp2, std::move(_result)) + 1);
        }
      }
      return _result;
    }

    /// quad_sum t sums all values in a quadtree.
    uint64_t quad_sum() const {
      const quadtree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const quadtree *_self;
      };

      /// CraneCont_Quad: saves [a1, a2, a3], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Quad {
        std::shared_ptr<quadtree> a1;
        std::shared_ptr<quadtree> a2;
        std::shared_ptr<quadtree> a3;
      };

      /// CraneCont_Quad_1: saves [_tmp4, a2, a3], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Quad_1 {
        uint64_t _tmp4;
        std::shared_ptr<quadtree> a2;
        std::shared_ptr<quadtree> a3;
      };

      /// CraneCont_Quad_2: saves [_tmp3, _tmp4, a3], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_Quad_2 {
        uint64_t _tmp3;
        uint64_t _tmp4;
        std::shared_ptr<quadtree> a3;
      };

      /// CraneCont_Quad_3: saves [_tmp2, _tmp3, _tmp4], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_Quad_3 {
        uint64_t _tmp2;
        uint64_t _tmp3;
        uint64_t _tmp4;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Quad, CraneCont_Quad_1,
                       CraneCont_Quad_2, CraneCont_Quad_3>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified quad_sum: CraneEnter -> CraneCont_Quad -> CraneCont_Quad_1
      /// -> CraneCont_Quad_2 -> CraneCont_Quad_3.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const quadtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename quadtree::QLeaf>(_sv.v());
            _result = std::move(a0);
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename quadtree::Quad>(_sv.v());
            _stack.emplace_back(CraneCont_Quad{a1, a2, a3});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Quad>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Quad>(_frame));
          std::shared_ptr<quadtree> a1 = std::move(_f.a1);
          std::shared_ptr<quadtree> a2 = std::move(_f.a2);
          std::shared_ptr<quadtree> a3 = std::move(_f.a3);
          _stack.emplace_back(CraneCont_Quad_1{std::move(_result),
                                               std::move(a2), std::move(a3)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_Quad_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Quad_1>(_frame));
          std::shared_ptr<quadtree> a2 = std::move(_f.a2);
          std::shared_ptr<quadtree> a3 = std::move(_f.a3);
          _stack.emplace_back(
              CraneCont_Quad_2{std::move(_result), _f._tmp4, std::move(a3)});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else if (std::holds_alternative<CraneCont_Quad_2>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Quad_2>(_frame));
          std::shared_ptr<quadtree> a3 = std::move(_f.a3);
          _stack.emplace_back(
              CraneCont_Quad_3{std::move(_result), _f._tmp3, _f._tmp4});
          _stack.emplace_back(CraneEnter{crane_raw(a3)});
        } else {
          auto _f = std::move(std::get<CraneCont_Quad_3>(_frame));
          _result = (_f._tmp4 + (_f._tmp3 + (_f._tmp2 + std::move(_result))));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
    T1 quadtree_rec(F0 &&f, F1 &&f0) const {
      return this->template quadtree_rect<T1>(f, f0);
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
    T1 quadtree_rect(F0 &&f, F1 &&f0) const {
      const quadtree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const quadtree *_self;
      };

      /// CraneCont_Quad: saves [a0, a1, a2, a3], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Quad {
        std::shared_ptr<quadtree> a0;
        std::shared_ptr<quadtree> a1;
        std::shared_ptr<quadtree> a2;
        std::shared_ptr<quadtree> a3;
      };

      /// CraneCont_Quad_1: saves [_tmp4, a0, a1, a2, a3], resumes after
      /// recursive call, then processes rest.
      struct CraneCont_Quad_1 {
        T1 _tmp4;
        std::shared_ptr<quadtree> a0;
        std::shared_ptr<quadtree> a1;
        std::shared_ptr<quadtree> a2;
        std::shared_ptr<quadtree> a3;
      };

      /// CraneCont_Quad_2: saves [_tmp3, _tmp4, a0, a1, a2, a3], resumes after
      /// recursive call, then processes rest.
      struct CraneCont_Quad_2 {
        T1 _tmp3;
        T1 _tmp4;
        std::shared_ptr<quadtree> a0;
        std::shared_ptr<quadtree> a1;
        std::shared_ptr<quadtree> a2;
        std::shared_ptr<quadtree> a3;
      };

      /// CraneCont_Quad_3: saves [_tmp2, _tmp3, _tmp4, a0, a1, a2, a3], resumes
      /// after recursive call, then processes rest.
      struct CraneCont_Quad_3 {
        T1 _tmp2;
        T1 _tmp3;
        T1 _tmp4;
        std::shared_ptr<quadtree> a0;
        std::shared_ptr<quadtree> a1;
        std::shared_ptr<quadtree> a2;
        std::shared_ptr<quadtree> a3;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Quad, CraneCont_Quad_1,
                       CraneCont_Quad_2, CraneCont_Quad_3>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified quadtree_rect: CraneEnter -> CraneCont_Quad ->
      /// CraneCont_Quad_1 -> CraneCont_Quad_2 -> CraneCont_Quad_3.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const quadtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename quadtree::QLeaf>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename quadtree::Quad>(_sv.v());
            _stack.emplace_back(CraneCont_Quad{a0, a1, a2, a3});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Quad>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Quad>(_frame));
          std::shared_ptr<quadtree> a0 = std::move(_f.a0);
          std::shared_ptr<quadtree> a1 = std::move(_f.a1);
          std::shared_ptr<quadtree> a2 = std::move(_f.a2);
          std::shared_ptr<quadtree> a3 = std::move(_f.a3);
          _stack.emplace_back(CraneCont_Quad_1{std::move(_result),
                                               std::move(a0), a1, std::move(a2),
                                               std::move(a3)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<CraneCont_Quad_1>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Quad_1>(_frame));
          std::shared_ptr<quadtree> a0 = std::move(_f.a0);
          std::shared_ptr<quadtree> a1 = std::move(_f.a1);
          std::shared_ptr<quadtree> a2 = std::move(_f.a2);
          std::shared_ptr<quadtree> a3 = std::move(_f.a3);
          _stack.emplace_back(CraneCont_Quad_2{
              std::move(_result), std::move(_f._tmp4), std::move(a0),
              std::move(a1), a2, std::move(a3)});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else if (std::holds_alternative<CraneCont_Quad_2>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Quad_2>(_frame));
          std::shared_ptr<quadtree> a0 = std::move(_f.a0);
          std::shared_ptr<quadtree> a1 = std::move(_f.a1);
          std::shared_ptr<quadtree> a2 = std::move(_f.a2);
          std::shared_ptr<quadtree> a3 = std::move(_f.a3);
          _stack.emplace_back(CraneCont_Quad_3{
              std::move(_result), std::move(_f._tmp3), std::move(_f._tmp4),
              std::move(a0), std::move(a1), std::move(a2), a3});
          _stack.emplace_back(CraneEnter{crane_raw(a3)});
        } else {
          auto _f = std::move(std::get<CraneCont_Quad_3>(_frame));
          std::shared_ptr<quadtree> a0 = std::move(_f.a0);
          std::shared_ptr<quadtree> a1 = std::move(_f.a1);
          std::shared_ptr<quadtree> a2 = std::move(_f.a2);
          std::shared_ptr<quadtree> a3 = std::move(_f.a3);
          _result = f0(*a0, std::move(_f._tmp4), *a1, std::move(_f._tmp3), *a2,
                       std::move(_f._tmp2), *a3, std::move(_result));
        }
      }
      return _result;
    }
  };

  /// Helper: max of 4 values using nested max.
  static uint64_t max4_impl(uint64_t a, uint64_t b, uint64_t c, uint64_t d);

  /// Simple binary tree with values only at leaves.
  struct simple_tree {
    // TYPES
    struct SLeaf {
      uint64_t a0;
    };

    struct SNode {
      std::shared_ptr<simple_tree> a0;
      std::shared_ptr<simple_tree> a1;
    };

    using variant_t = std::variant<SLeaf, SNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    simple_tree() {}

    explicit simple_tree(SLeaf _v) : v_(std::move(_v)) {}

    explicit simple_tree(SNode _v) : v_(std::move(_v)) {}

    static simple_tree sleaf(uint64_t a0) { return simple_tree(SLeaf{a0}); }

    static simple_tree snode(simple_tree a0, simple_tree a1) {
      return simple_tree(SNode{std::make_shared<simple_tree>(std::move(a0)),
                               std::make_shared<simple_tree>(std::move(a1))});
    }

    // MANIPULATORS
    ~simple_tree() {
      crane::small_vector<std::shared_ptr<simple_tree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<SNode>(&_v)) {
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

    simple_tree(const simple_tree &) = default;
    simple_tree &operator=(const simple_tree &) = default;
    simple_tree(simple_tree &&) = default;
    simple_tree &operator=(simple_tree &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// count_paths_simple t n counts paths with sum n (simpler variant).
    uint64_t count_paths_simple(uint64_t n) const {
      const simple_tree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const simple_tree *_self;
        uint64_t n;
      };

      /// CraneCont1: saves [a1, n], resumes after recursive call, then
      /// processes rest.
      struct CraneCont1 {
        std::shared_ptr<simple_tree> a1;
        uint64_t n;
      };

      /// CraneCont2: saves [_tmp2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont2 {
        uint64_t _tmp2;
      };

      using CraneFrame = std::variant<CraneEnter, CraneCont1, CraneCont2>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self, n});
      /// Loopified count_paths_simple: CraneEnter -> CraneCont1 -> CraneCont2.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const simple_tree *_self = _f._self;
          uint64_t n = _f.n;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename simple_tree::SLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename simple_tree::SLeaf>(_sv.v());
            if (a0 == n) {
              _result = UINT64_C(1);
            } else {
              _result = UINT64_C(0);
            }
          } else {
            const auto &[a0, a1] =
                std::get<typename simple_tree::SNode>(_sv.v());
            if (n <= UINT64_C(0)) {
              _result = UINT64_C(0);
            } else {
              _stack.emplace_back(CraneCont1{a1, n});
              _stack.emplace_back(CraneEnter{
                  crane_raw(a0),
                  (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1))))});
            }
          }
        } else if (std::holds_alternative<CraneCont1>(_frame)) {
          auto _f = std::move(std::get<CraneCont1>(_frame));
          std::shared_ptr<simple_tree> a1 = std::move(_f.a1);
          uint64_t n = _f.n;
          _stack.emplace_back(CraneCont2{std::move(_result)});
          _stack.emplace_back(
              CraneEnter{crane_raw(a1),
                         (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1))))});
        } else {
          auto _f = std::move(std::get<CraneCont2>(_frame));
          _result = (_f._tmp2 + std::move(_result));
        }
      }
      return _result;
    }

    /// simple_tree_sum t sums all leaf values.
    uint64_t simple_tree_sum() const {
      const simple_tree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const simple_tree *_self;
      };

      /// CraneCont_SNode: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_SNode {
        std::shared_ptr<simple_tree> a1;
      };

      /// CraneCont_SNode_1: saves [_tmp2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_SNode_1 {
        uint64_t _tmp2;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_SNode, CraneCont_SNode_1>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified simple_tree_sum: CraneEnter -> CraneCont_SNode ->
      /// CraneCont_SNode_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const simple_tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename simple_tree::SLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename simple_tree::SLeaf>(_sv.v());
            _result = std::move(a0);
          } else {
            const auto &[a0, a1] =
                std::get<typename simple_tree::SNode>(_sv.v());
            _stack.emplace_back(CraneCont_SNode{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_SNode>(_frame)) {
          auto _f = std::move(std::get<CraneCont_SNode>(_frame));
          std::shared_ptr<simple_tree> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_SNode_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<CraneCont_SNode_1>(_frame));
          _result = (_f._tmp2 + std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
    T1 simple_tree_rec(F0 &&f, F1 &&f0) const {
      return this->template simple_tree_rect<T1>(f, f0);
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
    T1 simple_tree_rect(F0 &&f, F1 &&f0) const {
      const simple_tree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const simple_tree *_self;
      };

      /// CraneCont_SNode: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_SNode {
        std::shared_ptr<simple_tree> a0;
        std::shared_ptr<simple_tree> a1;
      };

      /// CraneCont_SNode_1: saves [_tmp2, a0, a1], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_SNode_1 {
        T1 _tmp2;
        std::shared_ptr<simple_tree> a0;
        std::shared_ptr<simple_tree> a1;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_SNode, CraneCont_SNode_1>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified simple_tree_rect: CraneEnter -> CraneCont_SNode ->
      /// CraneCont_SNode_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const simple_tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename simple_tree::SLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename simple_tree::SLeaf>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1] =
                std::get<typename simple_tree::SNode>(_sv.v());
            _stack.emplace_back(CraneCont_SNode{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_SNode>(_frame)) {
          auto _f = std::move(std::get<CraneCont_SNode>(_frame));
          std::shared_ptr<simple_tree> a0 = std::move(_f.a0);
          std::shared_ptr<simple_tree> a1 = std::move(_f.a1);
          _stack.emplace_back(
              CraneCont_SNode_1{std::move(_result), std::move(a0), a1});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<CraneCont_SNode_1>(_frame));
          std::shared_ptr<simple_tree> a0 = std::move(_f.a0);
          std::shared_ptr<simple_tree> a1 = std::move(_f.a1);
          _result = f0(*a0, std::move(_f._tmp2), *a1, std::move(_result));
        }
      }
      return _result;
    }
  };

  /// Helper: compute minimum of three values.
  static uint64_t min3(uint64_t a, uint64_t b, uint64_t c);
  /// Helper: compute maximum of three values.
  static uint64_t max3(uint64_t a, uint64_t b, uint64_t c);
  /// tree_min_max t finds minimum and maximum values in tree.
  static std::pair<uint64_t, uint64_t> tree_min_max(const tree<uint64_t> &t);
  /// all_paths_sum t sums all root-to-leaf path sums.
  static uint64_t all_paths_sum(const tree<uint64_t> &t);
  /// tree_contains x t checks if value exists in tree.
  static bool tree_contains(uint64_t x, const tree<uint64_t> &t);
};

#endif // INCLUDED_LOOPIFY_TREES
