#ifndef INCLUDED_COFIX_THIS_THUNK
#define INCLUDED_COFIX_THIS_THUNK

#include "lazy.h"
#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

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
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{
          d_a0, d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
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

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons{std::move(a0), std::make_unique<List<t_A>>(std::move(a1))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
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

  __attribute__((pure)) static Sseq<t_A> scons(t_A shead,
                                               const Sseq<t_A> &stail) {
    return Sseq(SCons{std::move(shead), std::make_shared<Sseq<t_A>>(stail)});
  }

  __attribute__((pure)) static Sseq<t_A>
  lazy_(std::function<Sseq<t_A>()> thunk) {
    return Sseq<t_A>(std::function<variant_t()>([=]() mutable -> variant_t {
      Sseq<t_A> _tmp = thunk();
      return _tmp.v();
    }));
  }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_lazyV_.force(); }

  t_A shead() const {
    const auto &[d_shead, d_stail] =
        std::get<typename Sseq<t_A>::SCons>(this->v());
    return d_shead;
  }

  __attribute__((pure)) Sseq<t_A> stail() const {
    const auto &[d_shead, d_stail] =
        std::get<typename Sseq<t_A>::SCons>(this->v());
    return Sseq<t_A>::lazy_([=]() mutable -> Sseq<t_A> { return *(d_stail); });
  }

  /// This will be methodified on sseq because first arg is sseq A
  /// and the module is eponymous.
  template <MapsTo<t_A, t_A> F0> t_A double_head(F0 &&f) const {
    return f(this->shead());
  }

  template <MapsTo<t_A, t_A> F0>
  __attribute__((pure)) Sseq<t_A> smap(F0 &&f) const {
    Sseq<t_A> _self = *(this);
    return Sseq<t_A>::lazy_([=]() mutable -> Sseq<t_A> {
      return Sseq<t_A>::scons(_self.double_head(f), _self.stail().smap(f));
    });
  }

  template <MapsTo<t_A, t_A> F0>
  __attribute__((pure)) Sseq<t_A> smap_direct(F0 &&f) const {
    Sseq<t_A> _self = *(this);
    return Sseq<t_A>::lazy_([=]() mutable -> Sseq<t_A> {
      return Sseq<t_A>::scons(f(_self.shead()), _self.stail().smap_direct(f));
    });
  }

  /// Take n elements
  __attribute__((pure)) List<t_A> take(const unsigned int &n) const {
    if (n <= 0) {
      return List<t_A>::nil();
    } else {
      unsigned int m = n - 1;
      return List<t_A>::cons(this->shead(), this->stail().take(m));
    }
  }

  __attribute__((pure)) static Sseq<unsigned int> nats_from(unsigned int n) {
    return Sseq<unsigned int>::lazy_([=]() mutable -> Sseq<unsigned int> {
      return Sseq<unsigned int>::scons(n, nats_from((n + 1)));
    });
  }

  /// Sum of a list
  __attribute__((pure)) static unsigned int sum(const List<unsigned int> &l) {
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
