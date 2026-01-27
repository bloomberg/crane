#include <algorithm>
#include <any>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct List {
  template <typename A> struct list {
  public:
    struct nil {};
    struct cons {
      A _a0;
      std::shared_ptr<List::list<A>> _a1;
    };
    using variant_t = std::variant<nil, cons>;

  private:
    variant_t v_;
    explicit list(nil _v) : v_(std::move(_v)) {}
    explicit list(cons _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<List::list<A>> nil_() {
        return std::shared_ptr<List::list<A>>(new List::list<A>(nil{}));
      }
      static std::shared_ptr<List::list<A>>
      cons_(A a0, const std::shared_ptr<List::list<A>> &a1) {
        return std::shared_ptr<List::list<A>>(new List::list<A>(cons{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
  };
};

struct Sig0 {
  template <typename A> struct sig0 {
  public:
    struct exist {
      A _a0;
    };
    using variant_t = std::variant<exist>;

  private:
    variant_t v_;
    explicit sig0(exist _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Sig0::sig0<A>> exist_(A a0) {
        return std::shared_ptr<Sig0::sig0<A>>(new Sig0::sig0<A>(exist{a0}));
      }
    };
    const variant_t &v() const { return v_; }
  };
};

bool le_lt_dec(const unsigned int n, const unsigned int m);

std::shared_ptr<Sig0::sig0<std::shared_ptr<List::list<unsigned int>>>>
sort_cons_prog(const unsigned int a,
               const std::shared_ptr<List::list<unsigned int>> &_x,
               const std::shared_ptr<List::list<unsigned int>> &l_);

std::shared_ptr<Sig0::sig0<std::shared_ptr<List::list<unsigned int>>>>
isort(const std::shared_ptr<List::list<T1>> &l);
