#ifndef INCLUDED_TAIL_REC_REV
#define INCLUDED_TAIL_REC_REV

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

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

  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<t_A>> Nil_() {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::shared_ptr<List<t_A>>
    Cons_(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }

    static std::unique_ptr<List<t_A>> Nil_uptr() {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::unique_ptr<List<t_A>>
    Cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

template <typename T1>
std::shared_ptr<List<T1>> better_rev(const std::shared_ptr<List<T1>> &l) {
  std::function<std::shared_ptr<List<T1>>(std::shared_ptr<List<T1>>,
                                          std::shared_ptr<List<T1>>)>
      go;
  go = [&](std::shared_ptr<List<T1>> l0,
           std::shared_ptr<List<T1>> acc) -> std::shared_ptr<List<T1>> {
    return std::visit(
        Overloaded{[&](const typename List<T1>::Nil _args)
                       -> std::shared_ptr<List<T1>> { return std::move(acc); },
                   [&](const typename List<T1>::Cons _args)
                       -> std::shared_ptr<List<T1>> {
                     T1 x = _args.d_a0;
                     std::shared_ptr<List<T1>> xs = _args.d_a1;
                     return go(std::move(xs),
                               List<T1>::ctor::Cons_(x, std::move(acc)));
                   }},
        l0->v());
  };
  return go(l, List<T1>::ctor::Nil_());
}

#endif // INCLUDED_TAIL_REC_REV
