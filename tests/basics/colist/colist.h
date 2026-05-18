#ifndef INCLUDED_COLIST
#define INCLUDED_COLIST

#include "lazy.h"
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::unique_ptr<Nat> a0;
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

  Nat(const Nat &_other) : v_(std::move(_other.clone().v_)) {}

  Nat(Nat &&_other) noexcept : v_(std::move(_other.v_)) {}

  Nat &operator=(const Nat &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  Nat &operator=(Nat &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  Nat clone() const {
    Nat _out{};

    struct _CloneFrame {
      const Nat *_src;
      Nat *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const Nat *_src = _frame._src;
      Nat *_dst = _frame._dst;
      if (std::holds_alternative<O>(_src->v())) {
        _dst->v_ = O{};
      } else {
        const auto &_alt = std::get<S>(_src->v());
        _dst->v_ = S{_alt.a0 ? std::make_unique<Nat>() : nullptr};
        auto &_dst_alt = std::get<S>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  static Nat o() { return Nat(O{}); }

  static Nat s(Nat a0) { return Nat(S{std::make_unique<Nat>(std::move(a0))}); }

  // MANIPULATORS
  ~Nat() {
    std::vector<std::unique_ptr<Nat>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](Nat &_node) {
      if (std::holds_alternative<S>(_node.v_)) {
        auto &_alt = std::get<S>(_node.v_);
        if (_alt.a0) {
          _stack.push_back(std::move(_alt.a0));
        }
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node) {
        _drain(*_node);
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::unique_ptr<List<A>> l;
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

  List(const List<A> &_other) : v_(std::move(_other.clone().v_)) {}

  List(List<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  List<A> clone() const {
    List<A> _out{};

    struct _CloneFrame {
      const List<A> *_src;
      List<A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<A> *_src = _frame._src;
      List<A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->v_ = Cons{_alt.a, _alt.l ? std::make_unique<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.l) {
          _stack.push_back({_alt.l.get(), _dst_alt.l.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a), l ? std::make_unique<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_unique<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
        if (_alt.l) {
          _stack.push_back(std::move(_alt.l));
        }
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node) {
        _drain(*_node);
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename A> struct Colist {
  // TYPES
  struct Conil {};

  struct Cocons {
    A x;
    std::shared_ptr<Colist<A>> xs;
  };

  using variant_t = std::variant<Conil, Cocons>;

private:
  // DATA
  crane::lazy<variant_t> lazy_v_;

public:
  // CREATORS
  explicit Colist(Conil _v)
      : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

  explicit Colist(Cocons _v)
      : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

  explicit Colist(std::function<variant_t()> _thunk)
      : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

  static Colist<A> conil() { return Colist(Conil{}); }

  static Colist<A> cocons(A x, const Colist<A> &xs) {
    return Colist(Cocons{std::move(x), std::make_shared<Colist<A>>(xs)});
  }

  static Colist<A> lazy_(std::function<Colist<A>()> thunk) {
    return Colist<A>(std::function<variant_t()>([=]() mutable -> variant_t {
      Colist<A> _tmp = thunk();
      return _tmp.v();
    }));
  }

  // ACCESSORS
  const variant_t &v() const { return lazy_v_.force(); }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, A &>
  Colist<T1> comap(F0 &&f) const {
    if (std::holds_alternative<typename Colist<A>::Conil>(this->v())) {
      return Colist<T1>::lazy_(
          []() -> Colist<T1> { return Colist<T1>::conil(); });
    } else {
      const auto &[a0, a1] = std::get<typename Colist<A>::Cocons>(this->v());
      return Colist<T1>::lazy_([=]() mutable -> Colist<T1> {
        return Colist<T1>::cocons(f(a0), a1->template comap<T1>(f));
      });
    }
  }

  template <typename T1>
  static List<T1> list_of_colist(const Nat &fuel, Colist<T1> l) {
    if (std::holds_alternative<typename Nat::O>(fuel.v())) {
      return List<T1>::nil();
    } else {
      const auto &[a0] = std::get<typename Nat::S>(fuel.v());
      if (std::holds_alternative<typename Colist<T1>::Conil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[a00, a10] = std::get<typename Colist<T1>::Cocons>(l.v());
        return List<T1>::cons(a00, list_of_colist<T1>(*a0, *a10));
      }
    }
  }

  static Colist<Nat> nats(Nat n) {
    return Colist<Nat>::lazy_([=]() mutable -> Colist<Nat> {
      return Colist<Nat>::cocons(n, nats(Nat::s(n)));
    });
  }

  static const List<Nat> &first_three() {
    static const List<Nat> v =
        list_of_colist<Nat>(Nat::s(Nat::s(Nat::s(Nat::o()))), nats(Nat::o()));
    return v;
  }
};

#endif // INCLUDED_COLIST
