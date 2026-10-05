#ifndef INCLUDED_LOOPIFY_TREE_PATHS
#define INCLUDED_LOOPIFY_TREE_PATHS

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <algorithm>
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

struct LoopifyTreePaths {
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

    List<uint64_t> flatten_paths() const {
      const tree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const tree *_self;
      };

      /// CraneCont_Node: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Node {
        uint64_t a1;
        std::shared_ptr<tree> a2;
      };

      /// CraneCont_Node_1: saves [_tmp2, a1], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Node_1 {
        List<uint64_t> _tmp2;
        uint64_t a1;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
      List<uint64_t> _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified flatten_paths: CraneEnter -> CraneCont_Node ->
      /// CraneCont_Node_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = List<uint64_t>::nil();
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(CraneCont_Node{a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Node>(_frame));
          uint64_t a1 = _f.a1;
          std::shared_ptr<tree> a2 = std::move(_f.a2);
          _stack.emplace_back(CraneCont_Node_1{std::move(_result), a1});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
          uint64_t a1 = _f.a1;
          _result = List<uint64_t>::cons(
              a1, std::move(_f._tmp2).app(std::move(_result)));
        }
      }
      return _result;
    }

    uint64_t max_path_sum() const {
      const tree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const tree *_self;
      };

      /// CraneCont_Node: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Node {
        uint64_t a1;
        std::shared_ptr<tree> a2;
      };

      /// CraneCont_Node_1: saves [_tmp2, a1], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Node_1 {
        uint64_t _tmp2;
        uint64_t a1;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified max_path_sum: CraneEnter -> CraneCont_Node ->
      /// CraneCont_Node_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(CraneCont_Node{a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Node>(_frame));
          uint64_t a1 = _f.a1;
          std::shared_ptr<tree> a2 = std::move(_f.a2);
          _stack.emplace_back(CraneCont_Node_1{std::move(_result), a1});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
          uint64_t a1 = _f.a1;
          _result = (a1 + std::max(_f._tmp2, std::move(_result)));
        }
      }
      return _result;
    }

    std::optional<List<uint64_t>> find_path_sum(uint64_t acc,
                                                uint64_t target) const {
      const tree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const tree *_self;
        uint64_t acc;
      };

      /// CraneCont2: saves [a1], resumes after recursive call, then processes
      /// rest.
      struct CraneCont2 {
        uint64_t a1;
      };

      /// CraneCont_Node: saves [a1, a2, new_acc], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Node {
        uint64_t a1;
        std::shared_ptr<tree> a2;
        uint64_t new_acc;
      };

      using CraneFrame = std::variant<CraneEnter, CraneCont2, CraneCont_Node>;
      std::optional<List<uint64_t>> _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self, acc});
      /// Loopified find_path_sum: CraneEnter -> CraneCont2 -> CraneCont_Node.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const tree *_self = _f._self;
          uint64_t acc = _f.acc;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            if (acc == target) {
              _result =
                  std::make_optional<List<uint64_t>>(List<uint64_t>::nil());
            } else {
              _result = std::optional<List<uint64_t>>();
            }
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            uint64_t new_acc = (acc + a1);
            _stack.emplace_back(CraneCont_Node{a1, a2, new_acc});
            _stack.emplace_back(CraneEnter{crane_raw(a0), new_acc});
          }
        } else if (std::holds_alternative<CraneCont2>(_frame)) {
          auto _f = std::move(std::get<CraneCont2>(_frame));
          uint64_t a1 = _f.a1;
          std::optional<List<uint64_t>> _tmp1 = std::move(_result);
          if (_tmp1.has_value()) {
            const List<uint64_t> &path = *_tmp1;
            _result = std::make_optional<List<uint64_t>>(
                List<uint64_t>::cons(a1, path));
          } else {
            _result = std::optional<List<uint64_t>>();
          }
        } else {
          auto _f = std::move(std::get<CraneCont_Node>(_frame));
          uint64_t a1 = _f.a1;
          std::shared_ptr<tree> a2 = std::move(_f.a2);
          uint64_t new_acc = _f.new_acc;
          std::optional<List<uint64_t>> _tmp2 = std::move(_result);
          if (_tmp2.has_value()) {
            const List<uint64_t> &path = *_tmp2;
            _result = std::make_optional<List<uint64_t>>(
                List<uint64_t>::cons(a1, path));
          } else {
            _stack.emplace_back(CraneCont2{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a2), new_acc});
          }
        }
      }
      return _result;
    }

    uint64_t count_paths_sum(uint64_t target) const {
      return this->count_paths_sum_aux(UINT64_C(0), target);
    }

    uint64_t count_paths_sum_aux(uint64_t acc, uint64_t target) const {
      const tree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const tree *_self;
        uint64_t acc;
      };

      /// CraneCont_Node: saves [a2, new_acc], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Node {
        std::shared_ptr<tree> a2;
        uint64_t new_acc;
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
      _stack.emplace_back(CraneEnter{_self, acc});
      /// Loopified count_paths_sum_aux: CraneEnter -> CraneCont_Node ->
      /// CraneCont_Node_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const tree *_self = _f._self;
          uint64_t acc = _f.acc;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            if (acc == target) {
              _result = UINT64_C(1);
            } else {
              _result = UINT64_C(0);
            }
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            uint64_t new_acc = (acc + a1);
            _stack.emplace_back(CraneCont_Node{a2, new_acc});
            _stack.emplace_back(CraneEnter{crane_raw(a0), new_acc});
          }
        } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Node>(_frame));
          std::shared_ptr<tree> a2 = std::move(_f.a2);
          uint64_t new_acc = _f.new_acc;
          _stack.emplace_back(CraneCont_Node_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a2), new_acc});
        } else {
          auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
          _result = (_f._tmp2 + std::move(_result));
        }
      }
      return _result;
    }

    List<List<uint64_t>> paths() const {
      const tree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const tree *_self;
      };

      /// CraneCont_Node: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Node {
        uint64_t a1;
        std::shared_ptr<tree> a2;
      };

      /// CraneCont_Node_1: saves [_tmp2, a1], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Node_1 {
        List<List<uint64_t>> _tmp2;
        uint64_t a1;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
      List<List<uint64_t>> _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified paths: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = List<List<uint64_t>>::cons(List<uint64_t>::nil(),
                                                 List<List<uint64_t>>::nil());
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(CraneCont_Node{a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Node>(_frame));
          uint64_t a1 = _f.a1;
          std::shared_ptr<tree> a2 = std::move(_f.a2);
          _stack.emplace_back(CraneCont_Node_1{std::move(_result), a1});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
          uint64_t a1 = _f.a1;
          _result = map_cons(a1, std::move(_f._tmp2))
                        .app(map_cons(a1, std::move(_result)));
        }
      }
      return _result;
    }

    template <typename T1, typename F1> T1 tree_rec(T1 f, F1 &&f0) const {
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
        std::shared_ptr<tree> a2;
      };

      /// CraneCont_Node_1: saves [_tmp2, a0, a1, a2], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_Node_1 {
        T1 _tmp2;
        std::shared_ptr<tree> a0;
        uint64_t a1;
        std::shared_ptr<tree> a2;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified tree_rec: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
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
            _stack.emplace_back(CraneCont_Node{a0, a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Node>(_frame));
          std::shared_ptr<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          std::shared_ptr<tree> a2 = std::move(_f.a2);
          _stack.emplace_back(
              CraneCont_Node_1{std::move(_result), std::move(a0), a1, a2});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
          std::shared_ptr<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          std::shared_ptr<tree> a2 = std::move(_f.a2);
          _result = f0(*a0, std::move(_f._tmp2), a1, *a2, std::move(_result));
        }
      }
      return _result;
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
        std::shared_ptr<tree> a2;
      };

      /// CraneCont_Node_1: saves [_tmp2, a0, a1, a2], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_Node_1 {
        T1 _tmp2;
        std::shared_ptr<tree> a0;
        uint64_t a1;
        std::shared_ptr<tree> a2;
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
            _stack.emplace_back(CraneCont_Node{a0, a1, a2});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Node>(_frame));
          std::shared_ptr<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          std::shared_ptr<tree> a2 = std::move(_f.a2);
          _stack.emplace_back(
              CraneCont_Node_1{std::move(_result), std::move(a0), a1, a2});
          _stack.emplace_back(CraneEnter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
          std::shared_ptr<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          std::shared_ptr<tree> a2 = std::move(_f.a2);
          _result = f0(*a0, std::move(_f._tmp2), a1, *a2, std::move(_result));
        }
      }
      return _result;
    }
  };

  static List<List<uint64_t>> map_cons(uint64_t x,
                                       const List<List<uint64_t>> &ll);

  struct bool_tree {
    // TYPES
    struct BLeaf {
      uint64_t a0;
    };

    struct BNode {
      std::shared_ptr<bool_tree> a0;
      std::shared_ptr<bool_tree> a1;
    };

    using variant_t = std::variant<BLeaf, BNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    bool_tree() {}

    explicit bool_tree(BLeaf _v) : v_(std::move(_v)) {}

    explicit bool_tree(BNode _v) : v_(std::move(_v)) {}

    static bool_tree bleaf(uint64_t a0) { return bool_tree(BLeaf{a0}); }

    static bool_tree bnode(bool_tree a0, bool_tree a1) {
      return bool_tree(BNode{std::make_shared<bool_tree>(std::move(a0)),
                             std::make_shared<bool_tree>(std::move(a1))});
    }

    // MANIPULATORS
    ~bool_tree() {
      crane::small_vector<std::shared_ptr<bool_tree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<BNode>(&_v)) {
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

    bool_tree(const bool_tree &) = default;
    bool_tree &operator=(const bool_tree &) = default;
    bool_tree(bool_tree &&) = default;
    bool_tree &operator=(bool_tree &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename F0>
      requires std::is_invocable_r_v<bool, F0 &, const uint64_t &>
    bool and_search(F0 &&p) const {
      const bool_tree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const bool_tree *_self;
      };

      /// CraneCont_BNode: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_BNode {
        std::shared_ptr<bool_tree> a1;
      };

      /// CraneCont_BNode_1: saves [_tmp2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_BNode_1 {
        bool _tmp2;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_BNode, CraneCont_BNode_1>;
      bool _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified and_search: CraneEnter -> CraneCont_BNode ->
      /// CraneCont_BNode_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const bool_tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename bool_tree::BLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename bool_tree::BLeaf>(_sv.v());
            _result = p(a0);
          } else {
            const auto &[a0, a1] = std::get<typename bool_tree::BNode>(_sv.v());
            _stack.emplace_back(CraneCont_BNode{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_BNode>(_frame)) {
          auto _f = std::move(std::get<CraneCont_BNode>(_frame));
          std::shared_ptr<bool_tree> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_BNode_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<CraneCont_BNode_1>(_frame));
          _result = (_f._tmp2 && std::move(_result));
        }
      }
      return _result;
    }

    template <typename F0>
      requires std::is_invocable_r_v<bool, F0 &, const uint64_t &>
    bool or_search(F0 &&p) const {
      const bool_tree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const bool_tree *_self;
      };

      /// CraneCont_BNode: saves [a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_BNode {
        std::shared_ptr<bool_tree> a1;
      };

      /// CraneCont_BNode_1: saves [_tmp2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_BNode_1 {
        bool _tmp2;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_BNode, CraneCont_BNode_1>;
      bool _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified or_search: CraneEnter -> CraneCont_BNode ->
      /// CraneCont_BNode_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const bool_tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename bool_tree::BLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename bool_tree::BLeaf>(_sv.v());
            _result = p(a0);
          } else {
            const auto &[a0, a1] = std::get<typename bool_tree::BNode>(_sv.v());
            _stack.emplace_back(CraneCont_BNode{a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_BNode>(_frame)) {
          auto _f = std::move(std::get<CraneCont_BNode>(_frame));
          std::shared_ptr<bool_tree> a1 = std::move(_f.a1);
          _stack.emplace_back(CraneCont_BNode_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<CraneCont_BNode_1>(_frame));
          _result = (_f._tmp2 || std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
    T1 bool_tree_rec(F0 &&f, F1 &&f0) const {
      const bool_tree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const bool_tree *_self;
      };

      /// CraneCont_BNode: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_BNode {
        std::shared_ptr<bool_tree> a0;
        std::shared_ptr<bool_tree> a1;
      };

      /// CraneCont_BNode_1: saves [_tmp2, a0, a1], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_BNode_1 {
        T1 _tmp2;
        std::shared_ptr<bool_tree> a0;
        std::shared_ptr<bool_tree> a1;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_BNode, CraneCont_BNode_1>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified bool_tree_rec: CraneEnter -> CraneCont_BNode ->
      /// CraneCont_BNode_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const bool_tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename bool_tree::BLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename bool_tree::BLeaf>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1] = std::get<typename bool_tree::BNode>(_sv.v());
            _stack.emplace_back(CraneCont_BNode{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_BNode>(_frame)) {
          auto _f = std::move(std::get<CraneCont_BNode>(_frame));
          std::shared_ptr<bool_tree> a0 = std::move(_f.a0);
          std::shared_ptr<bool_tree> a1 = std::move(_f.a1);
          _stack.emplace_back(
              CraneCont_BNode_1{std::move(_result), std::move(a0), a1});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<CraneCont_BNode_1>(_frame));
          std::shared_ptr<bool_tree> a0 = std::move(_f.a0);
          std::shared_ptr<bool_tree> a1 = std::move(_f.a1);
          _result = f0(*a0, std::move(_f._tmp2), *a1, std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
    T1 bool_tree_rect(F0 &&f, F1 &&f0) const {
      const bool_tree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const bool_tree *_self;
      };

      /// CraneCont_BNode: saves [a0, a1], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_BNode {
        std::shared_ptr<bool_tree> a0;
        std::shared_ptr<bool_tree> a1;
      };

      /// CraneCont_BNode_1: saves [_tmp2, a0, a1], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_BNode_1 {
        T1 _tmp2;
        std::shared_ptr<bool_tree> a0;
        std::shared_ptr<bool_tree> a1;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_BNode, CraneCont_BNode_1>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified bool_tree_rect: CraneEnter -> CraneCont_BNode ->
      /// CraneCont_BNode_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const bool_tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename bool_tree::BLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename bool_tree::BLeaf>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1] = std::get<typename bool_tree::BNode>(_sv.v());
            _stack.emplace_back(CraneCont_BNode{a0, a1});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_BNode>(_frame)) {
          auto _f = std::move(std::get<CraneCont_BNode>(_frame));
          std::shared_ptr<bool_tree> a0 = std::move(_f.a0);
          std::shared_ptr<bool_tree> a1 = std::move(_f.a1);
          _stack.emplace_back(
              CraneCont_BNode_1{std::move(_result), std::move(a0), a1});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else {
          auto _f = std::move(std::get<CraneCont_BNode_1>(_frame));
          std::shared_ptr<bool_tree> a0 = std::move(_f.a0);
          std::shared_ptr<bool_tree> a1 = std::move(_f.a1);
          _result = f0(*a0, std::move(_f._tmp2), *a1, std::move(_result));
        }
      }
      return _result;
    }
  };
};

#endif // INCLUDED_LOOPIFY_TREE_PATHS
