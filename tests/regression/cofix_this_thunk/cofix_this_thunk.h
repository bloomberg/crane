#ifndef INCLUDED_COFIX_THIS_THUNK
#define INCLUDED_COFIX_THIS_THUNK

#include "lazy.h"
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a0;
    std::unique_ptr<List<A>> a1;
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

  List(List<A> &&_other) : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) {
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
        _dst->v_ =
            Cons{_alt.a0, _alt.a1 ? std::make_unique<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.a1) {
          _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
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
      const auto &[a0, a1] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a0), a1 ? std::make_unique<List<A>>(*a1) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a0, List<A> a1) {
    return List(Cons{std::move(a0), std::make_unique<List<A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
        if (_alt.a1) {
          _stack.push_back(std::move(_alt.a1));
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

/// Module name "Sseq" matches coinductive "sseq" -> eponymous
template <typename A> struct Sseq {
  // TYPES
  struct SCons {
    A shead;
    std::shared_ptr<Sseq<A>> stail;
  };

  using variant_t = std::variant<SCons>;

private:
  // DATA
  crane::lazy<variant_t> lazy_v_;

public:
  // CREATORS
  explicit Sseq(SCons _v)
      : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

  explicit Sseq(std::function<variant_t()> _thunk)
      : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

  static Sseq<A> scons(A shead, const Sseq<A> &stail) {
    return Sseq(SCons{std::move(shead), std::make_shared<Sseq<A>>(stail)});
  }

  static Sseq<A> lazy_(std::function<Sseq<A>()> thunk) {
    return Sseq<A>(std::function<variant_t()>([=]() mutable -> variant_t {
      Sseq<A> _tmp = thunk();
      return _tmp.v();
    }));
  }

  // ACCESSORS
  const variant_t &v() const { return lazy_v_.force(); }

  A shead() const {
    const auto &[shead1, stail0] = std::get<typename Sseq<A>::SCons>(this->v());
    return shead1;
  }

  Sseq<A> stail() const {
    const auto &[shead0, stail1] = std::get<typename Sseq<A>::SCons>(this->v());
    return Sseq<A>::lazy_([=]() mutable -> Sseq<A> { return *stail1; });
  }

  /// This will be methodified on sseq because first arg is sseq A
  /// and the module is eponymous.
  template <typename F0>
    requires std::is_invocable_r_v<A, F0 &, A &>
  A double_head(F0 &&f) const {
    return f(this->shead());
  }

  template <typename F0>
    requires std::is_invocable_r_v<A, F0 &, A &>
  Sseq<A> smap(F0 &&f) const {
    Sseq<A> _self_val = *this;
    return Sseq<A>::lazy_([=]() mutable -> Sseq<A> {
      return Sseq<A>::scons(_self_val.double_head(f),
                            _self_val.stail().smap(f));
    });
  }

  template <typename F0>
    requires std::is_invocable_r_v<A, F0 &, A &>
  Sseq<A> smap_direct(F0 &&f) const {
    Sseq<A> _self_val = *this;
    return Sseq<A>::lazy_([=]() mutable -> Sseq<A> {
      return Sseq<A>::scons(f(_self_val.shead()),
                            _self_val.stail().smap_direct(f));
    });
  }

  /// Take n elements
  List<A> take(unsigned int n) const {
    if (n <= 0) {
      return List<A>::nil();
    } else {
      unsigned int m = n - 1;
      return List<A>::cons(this->shead(), this->stail().take(m));
    }
  }

  static Sseq<unsigned int> nats_from(unsigned int n) {
    return Sseq<unsigned int>::lazy_([=]() mutable -> Sseq<unsigned int> {
      return Sseq<unsigned int>::scons(n, nats_from((n + 1)));
    });
  }

  /// Sum of a list
  static unsigned int sum(const List<unsigned int> &l) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
      return 0u;
    } else {
      const auto &[a0, a1] = std::get<typename List<unsigned int>::Cons>(l.v());
      return (a0 + sum(*a1));
    }
  }

  /// test1: smap (nats_from 0) S gives 1, 2, 3, 4, ...
  /// take 4 -> 1, 2, 3, 4 -> sum = 10
  static const unsigned int &test1() {
    static const unsigned int v = []() {
      Sseq<unsigned int> s =
          nats_from(0u).smap([](unsigned int x) { return (x + 1); });
      return sum(s.take(4u));
    }();
    return v;
  }

  /// test2: smap_direct (nats_from 0) S gives 1, 2, 3, 4, ...
  /// take 4 -> 1, 2, 3, 4 -> sum = 10
  static const unsigned int &test2() {
    static const unsigned int v = []() {
      Sseq<unsigned int> s =
          nats_from(0u).smap_direct([](unsigned int x) { return (x + 1); });
      return sum(s.take(4u));
    }();
    return v;
  }
};

#endif // INCLUDED_COFIX_THIS_THUNK
