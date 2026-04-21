#ifndef INCLUDED_COFIX_THIS_THUNK
#define INCLUDED_COFIX_THIS_THUNK

#include "lazy.h"
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

/// Module name "Sseq" matches coinductive "sseq" -> eponymous
template <typename t_A>
struct Sseq : public std::enable_shared_from_this<Sseq<t_A>> {
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

  static std::shared_ptr<Sseq<t_A>>
  scons(t_A shead, const std::shared_ptr<Sseq<t_A>> &stail) {
    return std::make_shared<Sseq<t_A>>(SCons{std::move(shead), stail});
  }

  static std::shared_ptr<Sseq<t_A>> scons(t_A shead,
                                          std::shared_ptr<Sseq<t_A>> &&stail) {
    return std::make_shared<Sseq<t_A>>(
        SCons{std::move(shead), std::move(stail)});
  }

  static std::shared_ptr<Sseq<t_A>>
  lazy_(std::function<std::shared_ptr<Sseq<t_A>>()> thunk) {
    return std::make_shared<Sseq<t_A>>(
        std::function<variant_t()>([=]() mutable -> variant_t {
          std::shared_ptr<Sseq<t_A>> _tmp = thunk();
          return _tmp->v();
        }));
  }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_lazyV_.force(); }

  t_A shead() const {
    const auto &[d_shead, d_stail] =
        std::get<typename Sseq<t_A>::SCons>(this->v());
    return d_shead;
  }

  std::shared_ptr<Sseq<t_A>> stail() const {
    const auto &[d_shead, d_stail] =
        std::get<typename Sseq<t_A>::SCons>(this->v());
    return Sseq<t_A>::lazy_(
        [=]() mutable -> std::shared_ptr<Sseq<t_A>> { return d_stail; });
  }

  /// This will be methodified on sseq because first arg is sseq A
  /// and the module is eponymous.
  template <MapsTo<t_A, t_A> F0> t_A double_head(F0 &&f) const {
    return f(this->shead());
  }

  template <MapsTo<t_A, t_A> F0> std::shared_ptr<Sseq<t_A>> smap(F0 &&f) const {
    std::shared_ptr<Sseq<t_A>> _self =
        std::const_pointer_cast<Sseq<t_A>>(this->shared_from_this());
    return Sseq<t_A>::lazy_([=]() mutable -> std::shared_ptr<Sseq<t_A>> {
      return Sseq<t_A>::scons(_self->double_head(f), _self->stail()->smap(f));
    });
  }

  template <MapsTo<t_A, t_A> F0>
  std::shared_ptr<Sseq<t_A>> smap_direct(F0 &&f) const {
    std::shared_ptr<Sseq<t_A>> _self =
        std::const_pointer_cast<Sseq<t_A>>(this->shared_from_this());
    return Sseq<t_A>::lazy_([=]() mutable -> std::shared_ptr<Sseq<t_A>> {
      return Sseq<t_A>::scons(f(_self->shead()),
                              _self->stail()->smap_direct(f));
    });
  }

  /// Take n elements
  std::shared_ptr<List<t_A>> take(const unsigned int n) const {
    if (n <= 0) {
      return List<t_A>::nil();
    } else {
      unsigned int m = n - 1;
      return List<t_A>::cons(
          std::const_pointer_cast<Sseq<t_A>>(this->shared_from_this())->shead(),
          std::const_pointer_cast<Sseq<t_A>>(this->shared_from_this())
              ->stail()
              ->take(m));
    }
  }

  static std::shared_ptr<Sseq<unsigned int>> nats_from(const unsigned int n) {
    return Sseq<unsigned int>::lazy_(
        [=]() mutable -> std::shared_ptr<Sseq<unsigned int>> {
          return Sseq<unsigned int>::scons(n, nats_from((n + 1)));
        });
  }

  /// Sum of a list
  __attribute__((pure)) static unsigned int
  sum(const std::shared_ptr<List<unsigned int>> &l) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(l->v());
      return (d_a0 + sum(d_a1));
    }
  }

  /// test1: smap (nats_from 0) S gives 1, 2, 3, 4, ...
  /// take 4 -> 1, 2, 3, 4 -> sum = 10
  static const unsigned int &test1() {
    static const unsigned int v = []() {
      std::shared_ptr<Sseq<unsigned int>> s =
          nats_from(0u)->smap([](const unsigned int x) { return (x + 1); });
      return sum(s->take(4u));
    }();
    return v;
  }

  /// test2: smap_direct (nats_from 0) S gives 1, 2, 3, 4, ...
  /// take 4 -> 1, 2, 3, 4 -> sum = 10
  static const unsigned int &test2() {
    static const unsigned int v = []() {
      std::shared_ptr<Sseq<unsigned int>> s = nats_from(0u)->smap_direct(
          [](const unsigned int x) { return (x + 1); });
      return sum(s->take(4u));
    }();
    return v;
  }
};

#endif // INCLUDED_COFIX_THIS_THUNK
