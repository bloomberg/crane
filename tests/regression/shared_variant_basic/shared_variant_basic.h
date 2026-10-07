#ifndef INCLUDED_SHARED_VARIANT_BASIC
#define INCLUDED_SHARED_VARIANT_BASIC

#include "crane_fn.h"
#include "crane_variant.h"
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

struct ListDef {
  static List<uint64_t> seq(uint64_t start, uint64_t len);
};

struct Nat {};

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    crane::box<List<A>> l;
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
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? crane::box<List<A>>::make(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), crane::box<List<A>>::make(std::move(l))});
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

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const A &>
  List<T1> map(F0 &&f) const {
    std::optional<List<T1>> _root{};
    crane::box<List<T1>> *_write = nullptr;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (crane::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = List<T1>::nil();
        (_write ? *(*_write = crane::box<List<T1>>::make(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = crane::get<typename List<A>::Cons>(_sv.v());
        auto _cell = typename List<T1>::Cons(f(a0), nullptr);
        List<T1> &_node =
            (_write ? *(*_write = crane::box<List<T1>>::make(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &crane::get<typename List<T1>::Cons>(_node.v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }

  uint64_t length() const {
    const List<A> *_self = this;

    /// CraneEnter: captures varying parameters for each recursive call.
    struct CraneEnter {
      const List<A> *_self;
    };

    /// CraneCont_Cons: resumes after recursive call, then processes rest.
    struct CraneCont_Cons {};

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    uint64_t _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{_self});
    /// Loopified length: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (crane::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(crane::get<CraneEnter>(_frame));
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (crane::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = crane::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(CraneCont_Cons{});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(crane::get<CraneCont_Cons>(_frame));
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }
};

struct SharedVariantBasic {
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      crane::box<tree> a0;
      uint64_t a1;
      uint64_t a2;
      crane::box<tree> a3;
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

    static tree node(tree a0, uint64_t a1, uint64_t a2, tree a3) {
      return tree(Node{crane::box<tree>::make(std::move(a0)), a1, a2,
                       crane::box<tree>::make(std::move(a3))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
  static T1 tree_rect(T1 f, F1 &&f0, const tree &t) {
    if (crane::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[a0, a1, a2, a3] = crane::get<typename tree::Node>(t.v());
      return f0(*a0, tree_rect<T1>(f, f0, *a0), a1, a2, *a3,
                tree_rect<T1>(f, f0, *a3));
    }
  }

  template <typename T1, typename F1>
  static T1 tree_rec(T1 f, F1 &&f0, const tree &t) {
    return tree_rect<T1>(std::move(f), f0, t);
  }

  static tree insert(uint64_t k, uint64_t v, const tree &t);
  static std::optional<uint64_t> find(uint64_t k, const tree &t);
  static uint64_t size(const tree &t);
  static inline const tree t0 =
      List<uint64_t>::cons(
          UINT64_C(5),
          List<uint64_t>::cons(
              UINT64_C(3),
              List<uint64_t>::cons(
                  UINT64_C(8),
                  List<uint64_t>::cons(
                      UINT64_C(1),
                      List<uint64_t>::cons(
                          UINT64_C(4),
                          List<uint64_t>::cons(
                              UINT64_C(7),
                              List<uint64_t>::cons(UINT64_C(9),
                                                   List<uint64_t>::nil())))))))
          .template fold_left<tree>(
              [](const tree &t, uint64_t k) {
                return insert(k, (k * UINT64_C(10)), t);
              },
              tree::leaf());
  static inline const tree t1 = insert(UINT64_C(4), UINT64_C(44), t0);
  static inline const uint64_t tree_result = []() -> uint64_t {
    auto _cs = find(UINT64_C(4), t0);
    if (_cs.has_value()) {
      const uint64_t &a = *_cs;
      auto _cs1 = find(UINT64_C(4), t1);
      if (_cs1.has_value()) {
        const uint64_t &b = *_cs1;
        auto _cs2 = find(UINT64_C(9), t1);
        if (_cs2.has_value()) {
          const uint64_t &c = *_cs2;
          return ((((a + b) + c) + size(t0)) + size(t1));
        } else {
          return UINT64_C(0);
        }
      } else {
        return UINT64_C(0);
      }
    } else {
      return UINT64_C(0);
    }
  }();
  static List<uint64_t> bump(const List<uint64_t> &l);
  static inline const uint64_t list_result =
      bump(List<uint64_t>::cons(
               UINT64_C(1),
               List<uint64_t>::cons(
                   UINT64_C(2),
                   List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()))))
          .template fold_left<uint64_t>(
              [](uint64_t _x0, uint64_t _x1) -> uint64_t {
                return (_x0 + _x1);
              },
              UINT64_C(0));
  static uint64_t long_result(uint64_t n);
};

#endif // INCLUDED_SHARED_VARIANT_BASIC
