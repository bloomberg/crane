#ifndef INCLUDED_TAIL_REC_ZIP
#define INCLUDED_TAIL_REC_ZIP

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

template <typename t_A, typename t_B> struct Prod {
  // TYPES
  struct Pair {
    t_A d_a0;
    t_B d_a1;
  };

  using variant_t = std::variant<Pair>;

private:
  // DATA
  variant_t d_v_;

  // CREATORS
  explicit Prod(Pair _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<Prod<t_A, t_B>> Pair_(t_A a0, t_B a1) {
      return std::shared_ptr<Prod<t_A, t_B>>(new Prod<t_A, t_B>(Pair{a0, a1}));
    }

    static std::unique_ptr<Prod<t_A, t_B>> Pair_uptr(t_A a0, t_B a1) {
      return std::unique_ptr<Prod<t_A, t_B>>(new Prod<t_A, t_B>(Pair{a0, a1}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

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

  std::shared_ptr<List<t_A>> rev() const {
    return std::visit(
        Overloaded{[](const typename List<t_A>::Nil _args)
                       -> std::shared_ptr<List<t_A>> {
                     return List<t_A>::ctor::Nil_();
                   },
                   [](const typename List<t_A>::Cons _args)
                       -> std::shared_ptr<List<t_A>> {
                     t_A x = _args.d_a0;
                     std::shared_ptr<List<t_A>> l_ = _args.d_a1;
                     return std::move(l_)->rev()->app(
                         List<t_A>::ctor::Cons_(x, List<t_A>::ctor::Nil_()));
                   }},
        this->v());
  }

  std::shared_ptr<List<t_A>> app(std::shared_ptr<List<t_A>> m) const {
    return std::visit(
        Overloaded{[&](const typename List<t_A>::Nil _args)
                       -> std::shared_ptr<List<t_A>> { return m; },
                   [&](const typename List<t_A>::Cons _args)
                       -> std::shared_ptr<List<t_A>> {
                     t_A a = _args.d_a0;
                     std::shared_ptr<List<t_A>> l1 = _args.d_a1;
                     return List<t_A>::ctor::Cons_(a, std::move(l1)->app(m));
                   }},
        this->v());
  }
};

template <typename T1, typename T2>
std::shared_ptr<List<std::shared_ptr<Prod<T1, T2>>>>
better_zip(const std::shared_ptr<List<T1>> &la,
           const std::shared_ptr<List<T2>> &lb) {
  std::function<std::shared_ptr<List<std::shared_ptr<Prod<T1, T2>>>>(
      std::shared_ptr<List<T1>>, std::shared_ptr<List<T2>>,
      std::shared_ptr<List<std::shared_ptr<Prod<T1, T2>>>>)>
      go;
  go = [&](std::shared_ptr<List<T1>> la0, std::shared_ptr<List<T2>> lb0,
           std::shared_ptr<List<std::shared_ptr<Prod<T1, T2>>>> acc)
      -> std::shared_ptr<List<std::shared_ptr<Prod<T1, T2>>>> {
    return std::visit(
        Overloaded{
            [&](const typename List<T1>::Nil _args)
                -> std::shared_ptr<List<std::shared_ptr<Prod<T1, T2>>>> {
              return std::move(acc)->rev();
            },
            [&](const typename List<T1>::Cons _args)
                -> std::shared_ptr<List<std::shared_ptr<Prod<T1, T2>>>> {
              T1 x = _args.d_a0;
              std::shared_ptr<List<T1>> xs = _args.d_a1;
              return std::visit(
                  Overloaded{
                      [&](const typename List<T2>::Nil _args)
                          -> std::shared_ptr<
                              List<std::shared_ptr<Prod<T1, T2>>>> {
                        return std::move(acc)->rev();
                      },
                      [&](const typename List<T2>::Cons _args)
                          -> std::shared_ptr<
                              List<std::shared_ptr<Prod<T1, T2>>>> {
                        T2 y = _args.d_a0;
                        std::shared_ptr<List<T2>> ys = _args.d_a1;
                        return go(
                            std::move(xs), std::move(ys),
                            List<std::shared_ptr<Prod<T1, T2>>>::ctor::Cons_(
                                Prod<T1, T2>::ctor::Pair_(x, y),
                                std::move(acc)));
                      }},
                  lb0->v());
            }},
        la0->v());
  };
  return go(la, lb, List<std::shared_ptr<Prod<T1, T2>>>::ctor::Nil_());
}

#endif // INCLUDED_TAIL_REC_ZIP
