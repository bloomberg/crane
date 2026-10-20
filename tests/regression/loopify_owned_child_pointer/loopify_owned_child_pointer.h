#ifndef INCLUDED_LOOPIFY_OWNED_CHILD_POINTER
#define INCLUDED_LOOPIFY_OWNED_CHILD_POINTER

#include "crane_fn.h"
#include "crane_variant.h"
#include "fn.h"
#include "obj.h"
#include "shared_variant.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>

template <typename A> struct List;

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    crane::shared_box<List<A>> l;
  };

  using variant_t = crane::shared_variant<Nil, Cons>;

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
          if (crane::holds_alternative<typename List<CraneU>::Nil>(
                  _other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                crane::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{[&]() -> A {
                          if constexpr (crane_convertible<A, const CraneU &>) {
                            return crane_convert<A>(a);
                          } else {
                            throw std::logic_error(
                                "unreachable: inactive constructor field at "
                                "this instantiation");
                          }
                        }(),
                        (l ? crane::shared_box<List<A>>::make(
                                 crane_convert<List<A>>(*l))
                           : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(
        Cons{std::move(a), crane::shared_box<List<A>>::make(std::move(l))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &&, const A &>
  T1 fold_left(F0 &&f, T1 a0) const {
    const List<A> *_loop_self = this;
    T1 _loop_a0 = std::move(a0);
    while (true) {
      auto &&_sv = *_loop_self;
      if (crane::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        return _loop_a0;
      } else {
        const auto &[a1, a2] = crane::get<typename List<A>::Cons>(_sv.v());
        _loop_self = crane_raw(a2);
        _loop_a0 = f(std::move(_loop_a0), a1);
      }
    }
  }

  List<A> app(List<A> m) const {
    std::optional<List<A>> _root{};
    crane::shared_box<List<A>> *_write = nullptr;
    const List<A> *_loop_self = this;
    List<A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (crane::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = std::move(_loop_m);
        (_write
             ? *(*_write = crane::shared_box<List<A>>::make(std::move(_value)))
             : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = crane::get<typename List<A>::Cons>(_sv.v());
        auto _cell = typename List<A>::Cons(a0, nullptr);
        List<A> &_node = (_write ? *(*_write = crane::shared_box<List<A>>::make(
                                         std::move(_cell)))
                                 : _root.emplace(std::move(_cell)));
        _write = &crane::get<typename List<A>::Cons>(_node.v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }
};

struct LoopifyOwnedChildPointer {
  struct t {
    // TYPES
    struct N {
      uint64_t a0;
      std::shared_ptr<std::pair<t, t>> a1;
    };

    struct E {};

    using variant_t = crane::shared_variant<N, E>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    t() {}

    explicit t(N _v) : v_(std::move(_v)) {}

    explicit t(E _v) : v_(_v) {}

    static t n(uint64_t a0, std::pair<t, t> a1) {
      return t(N{a0, std::make_shared<std::pair<t, t>>(std::move(a1))});
    }

    static t e() { return t(E{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t sz() const {
      const t *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const t *_self;
      };

      /// CraneCont_a: saves [a0, b], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_a {
        uint64_t a0;
        const t *b;
      };

      /// CraneCont_a_1: saves [_tmp2, a0], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_a_1 {
        uint64_t _tmp2;
        uint64_t a0;
      };

      using CraneFrame = std::variant<CraneEnter, CraneCont_a, CraneCont_a_1>;
      uint64_t _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified sz: CraneEnter -> CraneCont_a -> CraneCont_a_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (crane::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(crane::get<CraneEnter>(_frame));
          const t *_self = _f._self;
          auto &&_sv = *_self;
          if (crane::holds_alternative<typename t::N>(_sv.v())) {
            const auto &[a0, a1] = crane::get<typename t::N>(_sv.v());
            const auto &[a, b] = (*a1);
            _stack.emplace_back(CraneCont_a{a0, &b});
            _stack.emplace_back(CraneEnter{&a});
          } else {
            _result = UINT64_C(0);
          }
        } else if (crane::holds_alternative<CraneCont_a>(_frame)) {
          auto _f = std::move(crane::get<CraneCont_a>(_frame));
          uint64_t a0 = _f.a0;
          const t &b = *_f.b;
          _stack.emplace_back(CraneCont_a_1{std::move(_result), a0});
          _stack.emplace_back(CraneEnter{&b});
        } else {
          auto _f = std::move(crane::get<CraneCont_a_1>(_frame));
          uint64_t a0 = _f.a0;
          _result = ((a0 + _f._tmp2) + std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0> T1 t_rec(F0 &&f, T1 f0) const {
      return this->template t_rect<T1>(f, std::move(f0));
    }

    template <typename T1, typename F0> T1 t_rect(F0 &&f, T1 f0) const {
      if (crane::holds_alternative<typename t::N>(this->v())) {
        const auto &[a0, a1] = crane::get<typename t::N>(this->v());
        return f(a0, *a1);
      } else {
        return f0;
      }
    }
  };

  static t leaf(uint64_t n);

  struct reader {
    // DATA
    crane::fn<uint64_t(uint64_t)> a0;

    // ACCESSORS
    reader clone() const { return {a0}; }

    // CREATORS
    static reader reader0(crane::fn<uint64_t(uint64_t)> a0) {
      return {std::move(a0)};
    }

    uint64_t read(uint64_t k) const {
      const auto &[a0] = *this;
      return a0(k);
    }

    template <typename T1, typename F0> T1 reader_rec(F0 &&f) const {
      return this->template reader_rect<T1>(f);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &,
                                     const crane::fn<uint64_t(uint64_t)> &>
    T1 reader_rect(F0 &&f) const {
      const auto &[a0] = *this;
      return f(a0);
    }
  };

  static reader read_with(t x);
  static inline const uint64_t size =
      read_with(t::n(UINT64_C(2),
                     std::make_pair(leaf(UINT64_C(3)), leaf(UINT64_C(4)))))
          .read(UINT64_C(0));

  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      crane::shared_box<tree> a0;
      uint64_t a1;
      crane::shared_box<tree> a2;
    };

    using variant_t = crane::shared_variant<Leaf, Node>;

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
      return tree(Node{crane::shared_box<tree>::make(std::move(a0)), a1,
                       crane::shared_box<tree>::make(std::move(a2))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    List<crane::fn<uint64_t(uint64_t)>> subs() const {
      const tree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const tree *_self;
      };

      /// CraneCont_Node: saves [a0, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Node {
        crane::shared_box<tree> a0;
        const tree *a2;
      };

      /// CraneCont_Node_1: saves [_tmp2, a0], resumes after recursive call,
      /// then processes rest.
      struct CraneCont_Node_1 {
        List<crane::fn<uint64_t(uint64_t)>> _tmp2;
        crane::shared_box<tree> a0;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
      List<crane::fn<uint64_t(uint64_t)>> _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified subs: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (crane::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(crane::get<CraneEnter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (crane::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = List<crane::fn<uint64_t(uint64_t)>>::nil();
          } else {
            const auto &[a0, a1, a2] = crane::get<typename tree::Node>(_sv.v());
            const tree &a0_value = *a0;
            const tree &a2_value = *a2;
            _stack.emplace_back(CraneCont_Node{a0, crane_raw(a2)});
            _stack.emplace_back(CraneEnter{&a0_value});
          }
        } else if (crane::holds_alternative<CraneCont_Node>(_frame)) {
          auto _f = std::move(crane::get<CraneCont_Node>(_frame));
          crane::shared_box<tree> a0 = std::move(_f.a0);
          const tree &a2 = *_f.a2;
          const tree &a0_value = *a0;
          const tree &a2_value = a2;
          _stack.emplace_back(
              CraneCont_Node_1{std::move(_result), std::move(a0)});
          _stack.emplace_back(CraneEnter{&a2_value});
        } else {
          auto _f = std::move(crane::get<CraneCont_Node_1>(_frame));
          crane::shared_box<tree> a0 = std::move(_f.a0);
          const tree &a0_value = *a0;
          _result = List<crane::fn<uint64_t(uint64_t)>>::cons(
              [=](uint64_t y) { return (y + a0_value.sum()); },
              _f._tmp2.app(std::move(_result)));
        }
      }
      return _result;
    }

    uint64_t sum() const {
      const tree *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const tree *_self;
      };

      /// CraneCont_Node: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Node {
        uint64_t a1;
        const tree *a2;
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
      /// Loopified sum: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (crane::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(crane::get<CraneEnter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (crane::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2] = crane::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(CraneCont_Node{a1, crane_raw(a2)});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (crane::holds_alternative<CraneCont_Node>(_frame)) {
          auto _f = std::move(crane::get<CraneCont_Node>(_frame));
          uint64_t a1 = _f.a1;
          const tree &a2 = *_f.a2;
          _stack.emplace_back(CraneCont_Node_1{std::move(_result), a1});
          _stack.emplace_back(CraneEnter{_f.a2});
        } else {
          auto _f = std::move(crane::get<CraneCont_Node_1>(_frame));
          uint64_t a1 = _f.a1;
          _result = ((_f._tmp2 + a1) + std::move(_result));
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
        crane::shared_box<tree> a0;
        uint64_t a1;
        const tree *a2;
      };

      /// CraneCont_Node_1: saves [_tmp2, a0, a1, a2], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_Node_1 {
        T1 _tmp2;
        crane::shared_box<tree> a0;
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
        if (crane::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(crane::get<CraneEnter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (crane::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2] = crane::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(CraneCont_Node{a0, a1, crane_raw(a2)});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (crane::holds_alternative<CraneCont_Node>(_frame)) {
          auto _f = std::move(crane::get<CraneCont_Node>(_frame));
          crane::shared_box<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          const tree &a2 = *_f.a2;
          _stack.emplace_back(
              CraneCont_Node_1{std::move(_result), std::move(a0), a1, &a2});
          _stack.emplace_back(CraneEnter{_f.a2});
        } else {
          auto _f = std::move(crane::get<CraneCont_Node_1>(_frame));
          crane::shared_box<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          const tree &a2 = *_f.a2;
          _result = f0(*a0, std::move(_f._tmp2), a1, a2, std::move(_result));
        }
      }
      return _result;
    }
  };

  static inline const tree t0 = tree::node(
      tree::node(tree::leaf(), UINT64_C(1), tree::leaf()), UINT64_C(2),
      tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                 UINT64_C(4), tree::leaf()));

  static inline const uint64_t left_sums =
      t0.subs().template fold_left<uint64_t>(
          [](uint64_t a, const crane::fn<uint64_t(uint64_t)> &f) {
            return (a + f(UINT64_C(0)));
          },
          UINT64_C(0));
};

#endif // INCLUDED_LOOPIFY_OWNED_CHILD_POINTER
