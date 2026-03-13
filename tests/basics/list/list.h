#ifndef INCLUDED_LIST
#define INCLUDED_LIST

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

struct List {
  template <typename t_A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      t_A d_a0;
      std::shared_ptr<list<t_A>> d_a1;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit list(Nil _v) : d_v_(std::move(_v)) {}

    explicit list(Cons _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<list<t_A>> Nil_() {
        return std::shared_ptr<list<t_A>>(new list<t_A>(Nil{}));
      }

      static std::shared_ptr<list<t_A>>
      Cons_(t_A a0, const std::shared_ptr<list<t_A>> &a1) {
        return std::shared_ptr<list<t_A>>(new list<t_A>(Cons{a0, a1}));
      }

      static std::unique_ptr<list<t_A>> Nil_uptr() {
        return std::unique_ptr<list<t_A>>(new list<t_A>(Nil{}));
      }

      static std::unique_ptr<list<t_A>>
      Cons_uptr(t_A a0, const std::shared_ptr<list<t_A>> &a1) {
        return std::unique_ptr<list<t_A>>(new list<t_A>(Cons{a0, a1}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    t_A last(const t_A x) const {
      return std::visit(
          Overloaded{
              [&](const typename list<t_A>::Nil _args) -> t_A { return x; },
              [](const typename list<t_A>::Cons _args) -> t_A {
                t_A y = _args.d_a0;
                std::shared_ptr<list<t_A>> ls = _args.d_a1;
                return std::move(ls)->last(y);
              }},
          this->v());
    }

    t_A hd(const t_A x) const {
      return std::visit(
          Overloaded{
              [&](const typename list<t_A>::Nil _args) -> t_A { return x; },
              [](const typename list<t_A>::Cons _args) -> t_A {
                t_A y = _args.d_a0;
                return y;
              }},
          this->v());
    }

    template <typename T1, MapsTo<T1, t_A, std::shared_ptr<list<t_A>>, T1> F1>
    T1 list_rec(const T1 f, F1 &&f0) const {
      return std::visit(
          Overloaded{
              [&](const typename list<t_A>::Nil _args) -> T1 { return f; },
              [&](const typename list<t_A>::Cons _args) -> T1 {
                t_A y = _args.d_a0;
                std::shared_ptr<list<t_A>> l0 = _args.d_a1;
                return f0(y, l0, l0->template list_rec<T1>(f, f0));
              }},
          this->v());
    }

    template <typename T1, MapsTo<T1, t_A, std::shared_ptr<list<t_A>>, T1> F1>
    T1 list_rect(const T1 f, F1 &&f0) const {
      return std::visit(
          Overloaded{
              [&](const typename list<t_A>::Nil _args) -> T1 { return f; },
              [&](const typename list<t_A>::Cons _args) -> T1 {
                t_A y = _args.d_a0;
                std::shared_ptr<list<t_A>> l0 = _args.d_a1;
                return f0(y, l0, l0->template list_rect<T1>(f, f0));
              }},
          this->v());
    }

    std::shared_ptr<list<t_A>> tl() const {
      return std::visit(Overloaded{[](const typename list<t_A>::Nil _args)
                                       -> std::shared_ptr<list<t_A>> {
                                     return list<t_A>::ctor::Nil_();
                                   },
                                   [](const typename list<t_A>::Cons _args)
                                       -> std::shared_ptr<list<t_A>> {
                                     std::shared_ptr<list<t_A>> ls = _args.d_a1;
                                     return std::move(ls);
                                   }},
                        this->v());
    }

    std::shared_ptr<list<t_A>> app(std::shared_ptr<list<t_A>> l2) const {
      return std::visit(
          Overloaded{[&](const typename list<t_A>::Nil _args)
                         -> std::shared_ptr<list<t_A>> { return l2; },
                     [&](const typename list<t_A>::Cons _args)
                         -> std::shared_ptr<list<t_A>> {
                       t_A x = _args.d_a0;
                       std::shared_ptr<list<t_A>> l3 = _args.d_a1;
                       return list<t_A>::ctor::Cons_(x, std::move(l3)->app(l2));
                     }},
          this->v());
    }

    template <typename T1, MapsTo<T1, t_A> F0>
    std::shared_ptr<list<T1>> map(F0 &&f) const {
      return std::visit(Overloaded{[](const typename list<t_A>::Nil _args)
                                       -> std::shared_ptr<list<T1>> {
                                     return list<T1>::ctor::Nil_();
                                   },
                                   [&](const typename list<t_A>::Cons _args)
                                       -> std::shared_ptr<list<T1>> {
                                     t_A x = _args.d_a0;
                                     std::shared_ptr<list<t_A>> l_ = _args.d_a1;
                                     return list<T1>::ctor::Cons_(
                                         f(x),
                                         std::move(l_)->template map<T1>(f));
                                   }},
                        this->v());
    }
  };

  static inline const std::shared_ptr<list<unsigned int>> mytest =
      list<unsigned int>::ctor::Cons_(
          3u, list<unsigned int>::ctor::Cons_(
                  1u, list<unsigned int>::ctor::Cons_(
                          2u, list<unsigned int>::ctor::Nil_())))
          ->app(list<unsigned int>::ctor::Cons_(
              8u, list<unsigned int>::ctor::Cons_(
                      3u, list<unsigned int>::ctor::Cons_(
                              7u, list<unsigned int>::ctor::Cons_(
                                      9u, list<unsigned int>::ctor::Nil_())))));
};

#endif // INCLUDED_LIST
