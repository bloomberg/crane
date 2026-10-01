#ifndef INCLUDED_COFIX_THIS_THUNK
#define INCLUDED_COFIX_THIS_THUNK

#include "crane_fn.h"
#include "fn.h"
#include "lazy.h"
#include "obj.h"
#include <any>
#include <atomic>
#include <memory>
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

  template <typename _U>
  List(const List<_U> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const _U &>) {
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
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

/// Module name "Sseq" matches coinductive "sseq" -> eponymous
template <typename A> struct Sseq {
  // TYPES
  template <typename _S0 = Sseq<A>> struct SCons_ {
    A shead;
    _S0 stail;
  };

  using SCons = SCons_<>;
  using variant_t = std::variant<SCons>;

private:
  // DATA
  crane::lazy<variant_t> lazy_v_;

public:
  // CREATORS
  Sseq() {}

  explicit Sseq(SCons _v)
      : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

  template <typename _U>
  Sseq(const Sseq<_U> &_other)
      : lazy_v_(crane::lazy<variant_t>::converted_from(
            _other.lazy_cell(), [=]() -> variant_t {
              const auto &[shead, stail] =
                  std::get<typename Sseq<_U>::SCons>(_other.v());
              return SCons{[&]() -> A {
                             if constexpr (crane_convertible<A, const _U &>) {
                               return crane_convert<A>(shead);
                             } else {
                               throw std::logic_error(
                                   "unreachable: inactive constructor field at "
                                   "this instantiation");
                             }
                           }(),
                           crane_convert<Sseq<A>>(stail)};
            })) {}

  explicit Sseq(crane::fn<variant_t()> _thunk)
      : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

  static Sseq<A> scons(A shead, Sseq<A> stail) {
    return Sseq<A>(SCons{std::move(shead), std::move(stail)});
  }

  explicit Sseq(crane::lazy<variant_t> _cell) : lazy_v_(std::move(_cell)) {}

  template <typename F> static Sseq<A> lazy_(F &&thunk) {
    return Sseq<A>(crane::lazy<variant_t>::delegate(std::forward<F>(thunk)));
  }

  // ACCESSORS
  const variant_t &v() const { return lazy_v_.force(); }

  const crane::lazy<variant_t> &lazy_cell() const { return lazy_v_; }

  A shead() const {
    const auto &[shead1, stail0] = std::get<typename Sseq<A>::SCons>(this->v());
    return shead1;
  }

  Sseq<A> stail() const {
    const auto &[shead0, stail1] = std::get<typename Sseq<A>::SCons>(this->v());
    return stail1;
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
    return Sseq<A>::lazy_([=]() -> Sseq<A> {
      return Sseq<A>::scons(_self_val.double_head(f),
                            _self_val.stail().smap(f));
    });
  }

  template <typename F0>
    requires std::is_invocable_r_v<A, F0 &, A &>
  Sseq<A> smap_direct(F0 &&f) const {
    Sseq<A> _self_val = *this;
    return Sseq<A>::lazy_([=]() -> Sseq<A> {
      return Sseq<A>::scons(f(_self_val.shead()),
                            _self_val.stail().smap_direct(f));
    });
  }

  /// Take n elements
  List<A> take(uint64_t n) const {
    if (n <= 0) {
      return List<A>::nil();
    } else {
      uint64_t m = n - 1;
      return List<A>::cons(this->shead(), this->stail().take(m));
    }
  }

  static Sseq<uint64_t> nats_from(uint64_t n) {
    return Sseq<uint64_t>::lazy_([=]() -> Sseq<uint64_t> {
      return Sseq<uint64_t>::scons(n, nats_from((n + 1)));
    });
  }

  /// Sum of a list
  static uint64_t sum(const List<uint64_t> &l) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
      return (a0 + sum(*a1));
    }
  }

  /// test1: smap (nats_from 0) S gives 1, 2, 3, 4, ...
  /// take 4 -> 1, 2, 3, 4 -> sum = 10
  static const uint64_t &test1() {
    static const uint64_t v = []() {
      Sseq<uint64_t> s =
          nats_from(UINT64_C(0)).smap([](uint64_t x) { return (x + 1); });
      return sum(s.take(UINT64_C(4)));
    }();
    return v;
  }

  /// test2: smap_direct (nats_from 0) S gives 1, 2, 3, 4, ...
  /// take 4 -> 1, 2, 3, 4 -> sum = 10
  static const uint64_t &test2() {
    static const uint64_t v = []() {
      Sseq<uint64_t> s = nats_from(UINT64_C(0)).smap_direct([](uint64_t x) {
        return (x + 1);
      });
      return sum(s.take(UINT64_C(4)));
    }();
    return v;
  }
};

#endif // INCLUDED_COFIX_THIS_THUNK
