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

template <typename A> struct List {
public:
  struct nil {};
  struct cons {
    A _a0;
    std::shared_ptr<List<A>> _a1;
  };
  using variant_t = std::variant<nil, cons>;

private:
  variant_t v_;
  explicit List(nil _v) : v_(std::move(_v)) {}
  explicit List(cons _v) : v_(std::move(_v)) {}

public:
  struct ctor {
    ctor() = delete;
    static std::shared_ptr<List<A>> nil_() {
      return std::shared_ptr<List<A>>(new List<A>(nil{}));
    }
    static std::shared_ptr<List<A>> cons_(A a0,
                                          const std::shared_ptr<List<A>> &a1) {
      return std::shared_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
    static std::unique_ptr<List<A>> nil_uptr() {
      return std::unique_ptr<List<A>>(new List<A>(nil{}));
    }
    static std::unique_ptr<List<A>>
    cons_uptr(A a0, const std::shared_ptr<List<A>> &a1) {
      return std::unique_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
  };
  const variant_t &v() const { return v_; }
  variant_t &v_mut() { return v_; }
  std::shared_ptr<List<A>> firstn(const unsigned int n) const {
    if (n <= 0) {
      return List<A>::ctor::nil_();
    } else {
      unsigned int n0 = n - 1;
      return std::visit(
          Overloaded{
              [](const typename List<A>::nil _args)
                  -> std::shared_ptr<List<A>> { return List<A>::ctor::nil_(); },
              [&](const typename List<A>::cons _args)
                  -> std::shared_ptr<List<A>> {
                A a = _args._a0;
                std::shared_ptr<List<A>> l0 = _args._a1;
                return List<A>::ctor::cons_(a, std::move(l0)->firstn(n0));
              }},
          this->v());
    }
  }
  std::shared_ptr<List<A>> skipn(const unsigned int n) const {
    if (n <= 0) {
      return this;
    } else {
      unsigned int n0 = n - 1;
      return std::visit(Overloaded{[](const typename List<A>::nil _args)
                                       -> std::shared_ptr<List<A>> {
                                     return List<A>::ctor::nil_();
                                   },
                                   [&](const typename List<A>::cons _args)
                                       -> std::shared_ptr<List<A>> {
                                     std::shared_ptr<List<A>> l0 = _args._a1;
                                     return std::move(l0)->skipn(n0);
                                   }},
                        this->v());
    }
  }
  unsigned int length() const {
    return std::visit(
        Overloaded{
            [](const typename List<A>::nil _args) -> unsigned int { return 0; },
            [](const typename List<A>::cons _args) -> unsigned int {
              std::shared_ptr<List<A>> l_ = _args._a1;
              return (std::move(l_)->length() + 1);
            }},
        this->v());
  }
  std::shared_ptr<List<A>> app(std::shared_ptr<List<A>> m) const {
    return std::visit(Overloaded{[&](const typename List<A>::nil _args)
                                     -> std::shared_ptr<List<A>> { return m; },
                                 [&](const typename List<A>::cons _args)
                                     -> std::shared_ptr<List<A>> {
                                   A a = _args._a0;
                                   std::shared_ptr<List<A>> l1 = _args._a1;
                                   return List<A>::ctor::cons_(
                                       a, std::move(l1)->app(m));
                                 }},
                      this->v());
  }
};

struct UpdateNthOutOfBoundsLength {
  template <typename T1>
  static std::shared_ptr<List<T1>> update_nth(const unsigned int n, const T1 x,
                                              std::shared_ptr<List<T1>> l) {
    if ((n < l->length())) {
      return l->firstn(n)->app(List<T1>::ctor::cons_(x, l->skipn((n + 1))));
    } else {
      return std::move(l);
    }
  }

  static inline const unsigned int t =
      update_nth<unsigned int>(
          (((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
          (((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1),
          List<unsigned int>::ctor::cons_(
              (0 + 1),
              List<unsigned int>::ctor::cons_(
                  ((0 + 1) + 1),
                  List<unsigned int>::ctor::cons_(
                      (((0 + 1) + 1) + 1), List<unsigned int>::ctor::nil_()))))
          ->length();
};
