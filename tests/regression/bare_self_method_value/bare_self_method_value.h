#ifndef INCLUDED_BARE_SELF_METHOD_VALUE
#define INCLUDED_BARE_SELF_METHOD_VALUE

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct List;

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

  Nat add(Nat m) const {
    std::optional<Nat> _root{};
    std::shared_ptr<Nat> *_write = nullptr;
    const Nat *_loop_self = this;
    Nat _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        auto _value = std::move(_loop_m);
        (_write ? *(*_write = std::make_shared<Nat>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0] = std::get<typename Nat::S>(_sv.v());
        auto _cell = typename Nat::S(nullptr);
        Nat &_node =
            (_write ? *(*_write = std::make_shared<Nat>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename Nat::S>(_node.v_mut()).a0;
        _loop_self = crane_raw(a0);
        continue;
      }
    }
    return std::move(*_root);
  }
};

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

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &&, const A &>
  T1 fold_left(F0 &&f, T1 a0) const {
    const List<A> *_loop_self = this;
    T1 _loop_a0 = std::move(a0);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        return _loop_a0;
      } else {
        const auto &[a1, a2] = std::get<typename List<A>::Cons>(_sv.v());
        _loop_self = crane_raw(a2);
        _loop_a0 = f(std::move(_loop_a0), a1);
      }
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const A &>
  List<T1> map(F0 &&f) const {
    std::optional<List<T1>> _root{};
    std::shared_ptr<List<T1>> *_write = nullptr;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = List<T1>::nil();
        (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell = typename List<T1>::Cons(f(a0), nullptr);
        List<T1> &_node =
            (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<T1>::Cons>(_node.v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }
};

struct BareSelfMethodValue {
  struct bareSelfMethodValue {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<bareSelfMethodValue> a0;
      Nat a1;
      std::shared_ptr<bareSelfMethodValue> a2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    bareSelfMethodValue() {}

    explicit bareSelfMethodValue(Leaf _v) : v_(_v) {}

    explicit bareSelfMethodValue(Node _v) : v_(std::move(_v)) {}

    static bareSelfMethodValue leaf() { return bareSelfMethodValue(Leaf{}); }

    static bareSelfMethodValue node(bareSelfMethodValue a0, Nat a1,
                                    bareSelfMethodValue a2) {
      return bareSelfMethodValue(Node{
          std::make_shared<bareSelfMethodValue>(std::move(a0)), std::move(a1),
          std::make_shared<bareSelfMethodValue>(std::move(a2))});
    }

    // MANIPULATORS
    ~bareSelfMethodValue() {
      if (std::holds_alternative<Leaf>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<Node>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a2 && _alt->a2.use_count() == 1))) {
          return;
        }
      }
      crane::small_vector<std::shared_ptr<bareSelfMethodValue>> _stack = {};
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

    bareSelfMethodValue(const bareSelfMethodValue &) = default;
    bareSelfMethodValue &operator=(const bareSelfMethodValue &) = default;
    bareSelfMethodValue(bareSelfMethodValue &&) = default;
    bareSelfMethodValue &operator=(bareSelfMethodValue &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F1>
    T1 bareSelfMethodValue_rect(T1 f, F1 &&f0) const {
      const bareSelfMethodValue *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const bareSelfMethodValue *_self;
      };

      /// CraneCont_Node: saves [a0, a1, a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Node {
        std::shared_ptr<bareSelfMethodValue> a0;
        Nat a1;
        const bareSelfMethodValue *a2;
      };

      /// CraneCont_Node_1: saves [a0, a1, a2, _tmp2], resumes after recursive
      /// call, then processes rest.
      struct CraneCont_Node_1 {
        std::shared_ptr<bareSelfMethodValue> a0;
        Nat a1;
        const bareSelfMethodValue *a2;
        T1 _tmp2;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
      T1 _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified bareSelfMethodValue_rect: CraneEnter -> CraneCont_Node ->
      /// CraneCont_Node_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const bareSelfMethodValue *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename bareSelfMethodValue::Leaf>(
                  _sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename bareSelfMethodValue::Node>(_sv.v());
            _stack.emplace_back(CraneCont_Node{a0, a1, crane_raw(a2)});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Node>(_frame));
          std::shared_ptr<bareSelfMethodValue> a0 = std::move(_f.a0);
          Nat a1 = std::move(_f.a1);
          const bareSelfMethodValue &a2 = *_f.a2;
          _stack.emplace_back(CraneCont_Node_1{std::move(a0), std::move(a1),
                                               &a2, std::move(_result)});
          _stack.emplace_back(CraneEnter{_f.a2});
        } else {
          auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
          std::shared_ptr<bareSelfMethodValue> a0 = std::move(_f.a0);
          Nat a1 = std::move(_f.a1);
          const bareSelfMethodValue &a2 = *_f.a2;
          _result = f0(*a0, std::move(_f._tmp2), a1, a2, std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
    T1 bareSelfMethodValue_rec(T1 f, F1 &&f0) const {
      return this->template bareSelfMethodValue_rect<T1>(std::move(f), f0);
    }

    Nat size() const {
      const bareSelfMethodValue *_self = this;

      /// CraneEnter: captures varying parameters for each recursive call.
      struct CraneEnter {
        const bareSelfMethodValue *_self;
      };

      /// CraneCont_Node: saves [a2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Node {
        const bareSelfMethodValue *a2;
      };

      /// CraneCont_Node_1: saves [_tmp2], resumes after recursive call, then
      /// processes rest.
      struct CraneCont_Node_1 {
        Nat _tmp2;
      };

      using CraneFrame =
          std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
      Nat _result{};
      crane::small_vector<CraneFrame> _stack;
      _stack.emplace_back(CraneEnter{_self});
      /// Loopified size: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
      while (!_stack.empty()) {
        CraneFrame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<CraneEnter>(_frame)) {
          auto _f = std::move(std::get<CraneEnter>(_frame));
          const bareSelfMethodValue *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename bareSelfMethodValue::Leaf>(
                  _sv.v())) {
            _result = Nat::o();
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename bareSelfMethodValue::Node>(_sv.v());
            _stack.emplace_back(CraneCont_Node{crane_raw(a2)});
            _stack.emplace_back(CraneEnter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
          auto _f = std::move(std::get<CraneCont_Node>(_frame));
          const bareSelfMethodValue &a2 = *_f.a2;
          _stack.emplace_back(CraneCont_Node_1{std::move(_result)});
          _stack.emplace_back(CraneEnter{_f.a2});
        } else {
          auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
          _result = Nat::s(std::move(_f._tmp2).add(std::move(_result)));
        }
      }
      return _result;
    }
  };
  enum class Colour { RED, BLACK };

  template <typename T1> static T1 colour_rect(T1 f, T1 f0, Colour c) {
    switch (c) {
    case Colour::RED: {
      return f;
    }
    case Colour::BLACK: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 colour_rec(T1 f, T1 f0, Colour c) {
    return colour_rect<T1>(std::move(f), std::move(f0), c);
  }

  static List<Nat> sizes(const List<bareSelfMethodValue> &ts);
  static Nat total(const List<bareSelfMethodValue> &ts);
  static inline const Nat example = total(List<bareSelfMethodValue>::cons(
      bareSelfMethodValue::leaf(),
      List<bareSelfMethodValue>::cons(
          bareSelfMethodValue::node(bareSelfMethodValue::leaf(),
                                    Nat::s(Nat::o()),
                                    bareSelfMethodValue::leaf()),
          List<bareSelfMethodValue>::cons(
              bareSelfMethodValue::node(
                  bareSelfMethodValue::node(bareSelfMethodValue::leaf(),
                                            Nat::s(Nat::s(Nat::o())),
                                            bareSelfMethodValue::leaf()),
                  Nat::s(Nat::s(Nat::s(Nat::o()))),
                  bareSelfMethodValue::leaf()),
              List<bareSelfMethodValue>::nil()))));
};

#endif // INCLUDED_BARE_SELF_METHOD_VALUE
