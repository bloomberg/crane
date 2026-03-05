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

struct LoadProgramHeadWrite {
  struct state {
    std::shared_ptr<List<unsigned int>> rom;
    unsigned int prom_addr;
    unsigned int prom_data;
    bool prom_enable;
  };

  static std::shared_ptr<List<unsigned int>>
  rom(const std::shared_ptr<state> &s);

  static unsigned int prom_addr(const std::shared_ptr<state> &s);

  static unsigned int prom_data(const std::shared_ptr<state> &s);

  static bool prom_enable(const std::shared_ptr<state> &s);

  static std::shared_ptr<List<unsigned int>>
  update_nth(const unsigned int n, const unsigned int x,
             std::shared_ptr<List<unsigned int>> l);

  static std::shared_ptr<state> set_prom_params(std::shared_ptr<state> s,
                                                const unsigned int addr,
                                                const unsigned int data,
                                                const bool enable);

  static std::shared_ptr<state> execute_wpm(std::shared_ptr<state> s);

  static std::shared_ptr<state>
  load_program(std::shared_ptr<state> s, const unsigned int base,
               const std::shared_ptr<List<unsigned int>> &bytes);

  static inline const unsigned int t = [](void) {
    std::unique_ptr<state> s0 = std::make_unique<state>(
        state{List<unsigned int>::ctor::cons_(
                  0, List<unsigned int>::ctor::cons_(
                         0, List<unsigned int>::ctor::cons_(
                                0, List<unsigned int>::ctor::cons_(
                                       0, List<unsigned int>::ctor::nil_())))),
              0, 0, false});
    std::shared_ptr<state> s1 =
        load_program(std::move(s0), (0 + 1),
                     List<unsigned int>::ctor::cons_(
                         (((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1),
                         List<unsigned int>::ctor::cons_(
                             ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
                             List<unsigned int>::ctor::nil_())));
    return std::move(s1)->rom->nth((0 + 1), 0);
  }();
};
