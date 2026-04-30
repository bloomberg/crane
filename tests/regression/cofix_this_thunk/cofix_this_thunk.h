#ifndef INCLUDED_COFIX_THIS_THUNK
#define INCLUDED_COFIX_THIS_THUNK

#include "lazy.h"
#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  List<t_A> clone() const {
    List<t_A> _out{};

    struct _CloneFrame {
      const List<t_A> *_src;
      List<t_A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<t_A> *_src = _frame._src;
      List<t_A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->d_v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->d_v_ = Cons{_alt.d_a0,
                          _alt.d_a1 ? std::make_unique<List<t_A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->d_v_);
        if (_alt.d_a1) {
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  static List<t_A> nil() { return List(Nil{}); }

  static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons{std::move(a0), std::make_unique<List<t_A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<t_A>>> _stack{};
    auto _drain = [&](List<t_A> &_node) {
      if (std::holds_alternative<Cons>(_node.d_v_)) {
        auto &_alt = std::get<Cons>(_node.d_v_);
        if (_alt.d_a1) {
          _stack.push_back(std::move(_alt.d_a1));
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

  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }
};

/// Module name "Sseq" matches coinductive "sseq" -> eponymous
template <typename t_A> struct Sseq {
  // TYPES
  struct SCons {
    t_A d_shead;
    std::shared_ptr<Sseq<t_A>> d_stail;
  };

  using variant_t = std::variant<SCons>;

private:
  // DATA
  crane::lazy<variant_t> d_lazyV_;

public:
  // CREATORS
  explicit Sseq(SCons _v)
      : d_lazyV_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

  explicit Sseq(std::function<variant_t()> _thunk)
      : d_lazyV_(crane::lazy<variant_t>(std::move(_thunk))) {}

  static Sseq<t_A> scons(t_A shead, const Sseq<t_A> &stail) {
    return Sseq(SCons{std::move(shead), std::make_shared<Sseq<t_A>>(stail)});
  }

  static Sseq<t_A> lazy_(std::function<Sseq<t_A>()> thunk) {
    return Sseq<t_A>(std::function<variant_t()>([=]() mutable -> variant_t {
      Sseq<t_A> _tmp = thunk();
      return _tmp.v();
    }));
  }

  // ACCESSORS
  const variant_t &v() const { return d_lazyV_.force(); }

  t_A shead() const {
    const auto &[d_shead, d_stail] =
        std::get<typename Sseq<t_A>::SCons>(this->v());
    return d_shead;
  }

  Sseq<t_A> stail() const {
    const auto &[d_shead, d_stail] =
        std::get<typename Sseq<t_A>::SCons>(this->v());
    return Sseq<t_A>::lazy_([=]() mutable -> Sseq<t_A> { return *(d_stail); });
  }

  /// This will be methodified on sseq because first arg is sseq A
  /// and the module is eponymous.
  template <MapsTo<t_A, t_A> F0> t_A double_head(F0 &&f) const {
    return f(this->shead());
  }

  template <MapsTo<t_A, t_A> F0> Sseq<t_A> smap(F0 &&f) const {
    Sseq<t_A> _self = *(this);
    return Sseq<t_A>::lazy_([=]() mutable -> Sseq<t_A> {
      return Sseq<t_A>::scons(_self.double_head(f), _self.stail().smap(f));
    });
  }

  template <MapsTo<t_A, t_A> F0> Sseq<t_A> smap_direct(F0 &&f) const {
    Sseq<t_A> _self = *(this);
    return Sseq<t_A>::lazy_([=]() mutable -> Sseq<t_A> {
      return Sseq<t_A>::scons(f(_self.shead()), _self.stail().smap_direct(f));
    });
  }

  /// Take n elements
  List<t_A> take(const unsigned int &n) const {
    if (n <= 0) {
      return List<t_A>::nil();
    } else {
      unsigned int m = n - 1;
      return List<t_A>::cons(this->shead(), this->stail().take(m));
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
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(l.v());
      return (d_a0 + sum(*(d_a1)));
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
