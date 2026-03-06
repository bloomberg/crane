#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
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
  A nth(const unsigned int n, const A default0) const {
    if (n <= 0) {
      return std::visit(Overloaded{[&](const typename List<A>::nil _args) -> A {
                                     return default0;
                                   },
                                   [](const typename List<A>::cons _args) -> A {
                                     A x = _args._a0;
                                     return x;
                                   }},
                        this->v());
    } else {
      unsigned int m = n - 1;
      return std::visit(
          Overloaded{
              [&](const typename List<A>::nil _args) -> A { return default0; },
              [&](const typename List<A>::cons _args) -> A {
                std::shared_ptr<List<A>> l_ = _args._a1;
                return std::move(l_)->nth(m, default0);
              }},
          this->v());
    }
  }
};

struct Nat {
  static std::pair<unsigned int, unsigned int> divmod(const unsigned int x,
                                                      const unsigned int y,
                                                      const unsigned int q,
                                                      const unsigned int u);

  static unsigned int div(const unsigned int x, const unsigned int y);
};

struct RegisterPairEvenRounding {
  struct state {
    std::shared_ptr<List<unsigned int>> regs_;
  };

  static std::shared_ptr<List<unsigned int>>
  regs_(const std::shared_ptr<state> &s);

  template <typename T1>
  static std::shared_ptr<List<T1>>
  update_nth(const unsigned int n, const T1 x,
             const std::shared_ptr<List<T1>> &l) {
    if (n <= 0) {
      return std::visit(Overloaded{[](const typename List<T1>::nil _args)
                                       -> std::shared_ptr<List<T1>> {
                                     return List<T1>::ctor::nil_();
                                   },
                                   [&](const typename List<T1>::cons _args)
                                       -> std::shared_ptr<List<T1>> {
                                     std::shared_ptr<List<T1>> xs = _args._a1;
                                     return List<T1>::ctor::cons_(
                                         x, std::move(xs));
                                   }},
                        l->v());
    } else {
      unsigned int n_ = n - 1;
      return std::visit(Overloaded{[](const typename List<T1>::nil _args)
                                       -> std::shared_ptr<List<T1>> {
                                     return List<T1>::ctor::nil_();
                                   },
                                   [&](const typename List<T1>::cons _args)
                                       -> std::shared_ptr<List<T1>> {
                                     T1 y = _args._a0;
                                     std::shared_ptr<List<T1>> ys = _args._a1;
                                     return List<T1>::ctor::cons_(
                                         y,
                                         update_nth<T1>(n_, x, std::move(ys)));
                                   }},
                        l->v());
    }
  }

  static unsigned int get_reg(const std::shared_ptr<state> &s,
                              const unsigned int r);

  static std::shared_ptr<state>
  set_reg(std::shared_ptr<state> s, const unsigned int r, const unsigned int v);

  static unsigned int get_reg_pair(const std::shared_ptr<state> &s,
                                   const unsigned int r);

  static std::shared_ptr<state> set_reg_pair(const std::shared_ptr<state> &s,
                                             const unsigned int r,
                                             const unsigned int v);

  static inline const std::shared_ptr<state> sample =
      std::make_shared<state>(state{List<unsigned int>::ctor::cons_(
          0,
          List<unsigned int>::ctor::cons_(
              (0 + 1), List<unsigned int>::ctor::cons_(
                           ((0 + 1) + 1),
                           List<unsigned int>::ctor::cons_(
                               (((0 + 1) + 1) + 1),
                               List<unsigned int>::ctor::cons_(
                                   ((((0 + 1) + 1) + 1) + 1),
                                   List<unsigned int>::ctor::cons_(
                                       (((((0 + 1) + 1) + 1) + 1) + 1),
                                       List<unsigned int>::ctor::nil_()))))))});

  static inline const unsigned int t = get_reg_pair(
      set_reg_pair(
          sample, (((0 + 1) + 1) + 1),
          (((((((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) +
                                                   1) +
                                                  1) +
                                                 1) +
                                                1) +
                                               1) +
                                              1) +
                                             1) +
                                            1) +
                                           1) +
                                          1) +
                                         1) +
                                        1) +
                                       1) +
                                      1) +
                                     1) +
                                    1) +
                                   1) +
                                  1) +
                                 1) +
                                1) +
                               1) +
                              1) +
                             1) +
                            1) +
                           1) +
                          1) +
                         1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1)),
      (((0 + 1) + 1) + 1));
};
