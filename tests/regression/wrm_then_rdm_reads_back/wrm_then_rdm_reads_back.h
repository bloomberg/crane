#ifndef INCLUDED_WRM_THEN_RDM_READS_BACK
#define INCLUDED_WRM_THEN_RDM_READS_BACK

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
  // TYPES
  struct nil {};

  struct cons {
    A _a0;
    std::shared_ptr<List<A>> _a1;
  };

  using variant_t = std::variant<nil, cons>;

private:
  // DATA
  variant_t v_;

  // CREATORS
  explicit List(nil _v) : v_(std::move(_v)) {}

  explicit List(cons _v) : v_(std::move(_v)) {}

public:
  // TYPES
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

  // MANIPULATORS
  variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

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

struct WrmThenRdmReadsBack {
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

  struct state {
    std::shared_ptr<List<unsigned int>> regs;
    unsigned int acc;
    std::shared_ptr<List<unsigned int>> ram;
    unsigned int sel_char;
  };

  static unsigned int get_reg(const std::shared_ptr<state> &s,
                              const unsigned int r);
  static unsigned int get_reg_pair(const std::shared_ptr<state> &s,
                                   const unsigned int r);
  static std::shared_ptr<state> execute_src(std::shared_ptr<state> s,
                                            const unsigned int r);
  static std::shared_ptr<state> execute_wrm(std::shared_ptr<state> s);
  static std::shared_ptr<state> execute_rdm(std::shared_ptr<state> s);
  static inline const std::shared_ptr<state> sample =
      std::make_shared<state>(state{
          List<unsigned int>::ctor::cons_(
              0u,
              List<unsigned int>::ctor::cons_(
                  0u,
                  List<unsigned int>::ctor::cons_(
                      1u,
                      List<unsigned int>::ctor::cons_(
                          3u,
                          List<unsigned int>::ctor::cons_(
                              0u, List<unsigned int>::ctor::cons_(
                                      0u,
                                      List<unsigned int>::ctor::nil_())))))),
          12u,
          List<unsigned int>::ctor::cons_(
              0u,
              List<unsigned int>::ctor::cons_(
                  0u,
                  List<unsigned int>::ctor::cons_(
                      0u, List<unsigned int>::ctor::cons_(
                              5u, List<unsigned int>::ctor::cons_(
                                      0u, List<unsigned int>::ctor::nil_()))))),
          0u});
  static inline const std::shared_ptr<state> roundtrip =
      execute_rdm(execute_wrm(execute_src(sample, 3u)));
  static inline const bool t = (roundtrip->acc == 12u);
};

#endif // INCLUDED_WRM_THEN_RDM_READS_BACK
