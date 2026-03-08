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

struct RegPairSuccessor {
  struct state {
    std::shared_ptr<List<unsigned int>> regs;
  };

  static unsigned int get_reg(const std::shared_ptr<state> &s,
                              const unsigned int r);

  static unsigned int get_reg_pair(const std::shared_ptr<state> &s,
                                   const unsigned int r);

  static inline const std::shared_ptr<state> sample =
      std::make_shared<state>(state{List<unsigned int>::ctor::cons_(
          0u,
          List<unsigned int>::ctor::cons_(
              0u,
              List<unsigned int>::ctor::cons_(
                  10u,
                  List<unsigned int>::ctor::cons_(
                      11u,
                      List<unsigned int>::ctor::cons_(
                          0u, List<unsigned int>::ctor::cons_(
                                  0u, List<unsigned int>::ctor::nil_()))))))});

  static inline const bool even_same_as_successor =
      (get_reg_pair(sample, 2u) == get_reg_pair(sample, 3u));

  static inline const bool odd_same_as_predecessor =
      (get_reg_pair(sample, 3u) == get_reg_pair(sample, 2u));

  static inline const bool t =
      (even_same_as_successor && odd_same_as_predecessor);
};
