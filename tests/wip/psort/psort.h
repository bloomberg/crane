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

template <typename T1, typename T2, MapsTo<T2, T1> F1, MapsTo<T2, T1, T1> F2,
          MapsTo<T2, T1, T1, std::shared_ptr<List::list<T1>>, T2, T2> F3>
T2 div_conq_pair(const T2 x, F1 &&x0, F2 &&x1, F3 &&x2,
                 const std::shared_ptr<List::list<T1>> &l) {
  return std::visit(
      Overloaded{[&](const typename List::list<T1>::nil _args)
                     -> std::function<T2(
                         std::function<T2(std::shared_ptr<List::list<T1>>)>)> {
                   return x;
                 },
                 [&](const typename List::list<T1>::cons _args)
                     -> std::function<T2(
                         std::function<T2(std::shared_ptr<List::list<T1>>)>)> {
                   T1 a = _args._a0;
                   std::shared_ptr<List::list<T1>> l0 = _args._a1;
                   return std::visit(
                       Overloaded{
                           [&](const typename List::list<T1>::nil _args)
                               -> std::function<T2(
                                   std::function<T2(
                                       std::shared_ptr<List::list<T1>>)>)> {
                             return x0(a);
                           },
                           [&](const typename List::list<T1>::cons _args)
                               -> std::function<T2(
                                   std::function<T2(
                                       std::shared_ptr<List::list<T1>>)>)> {
                             T1 a0 = _args._a0;
                             std::shared_ptr<List::list<T1>> l1 = _args._a1;
                             return x2(
                                 a, a0, l1, x1(a, a0),
                                 div_conq_pair<T1, T2>(x, x0, x1, x2, l1));
                           }},
                       l0->v());
                 }},
      l->v());
}

std::shared_ptr<List::list<unsigned int>>
merge(const std::shared_ptr<List::list<unsigned int>> &l1,
      const std::shared_ptr<List::list<unsigned int>> &l2);

std::shared_ptr<Sig0::sig0<std::shared_ptr<List::list<unsigned int>>>>
pair_merge_prog(const unsigned int _x, const unsigned int _x0,
                const std::shared_ptr<List::list<unsigned int>> &_x1,
                const std::shared_ptr<List::list<unsigned int>> &l_,
                const std::shared_ptr<List::list<unsigned int>> &l_0);

std::shared_ptr<Sig0::sig0<std::shared_ptr<List::list<unsigned int>>>>
psort(const std::shared_ptr<List::list<unsigned int>> &);
