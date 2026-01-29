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

bool le_gt_dec(const unsigned int, const unsigned int);

bool le_dec(const unsigned int n, const unsigned int m);

template <typename T1, MapsTo<bool, T1, T1> F0>
std::pair<std::shared_ptr<List::list<T1>>, std::shared_ptr<List::list<T1>>>
split_pivot(F0 &&le_dec0, const T1 pivot,
            const std::shared_ptr<List::list<T1>> &l) {
  return std::visit(
      Overloaded{
          [](const typename List::list<T1>::nil _args)
              -> std::pair<std::shared_ptr<List::list<T1>>,
                           std::shared_ptr<List::list<T1>>> {
            return std::make_pair(List::list<T1>::ctor::nil_(),
                                  List::list<T1>::ctor::nil_());
          },
          [&](const typename List::list<T1>::cons _args)
              -> std::pair<std::shared_ptr<List::list<T1>>,
                           std::shared_ptr<List::list<T1>>> {
            T1 a = _args._a0;
            std::shared_ptr<List::list<T1>> l_ = _args._a1;
            std::shared_ptr<List::list<T1>> l1 =
                split_pivot<T1>(le_dec0, pivot, l_).first;
            std::shared_ptr<List::list<T1>> l2 =
                split_pivot<T1>(le_dec0, pivot, l_).second;
            if (le_dec0(a, pivot)) {
              return std::make_pair(List::list<T1>::ctor::cons_(a, l1), l2);
            } else {
              return std::make_pair(l1, List::list<T1>::ctor::cons_(a, l2));
            }
          }},
      l->v());
}

template <typename T1, typename T2, MapsTo<bool, T1, T1> F0,
          MapsTo<T2, T1, std::shared_ptr<List::list<T1>>, T2, T2> F2>
T2 div_conq_pivot(F0 &&le_dec0, const T2 x, F2 &&x0,
                  const std::shared_ptr<List::list<T1>> &l) {
  return std::visit(
      Overloaded{
          [&](const typename List::list<T1>::nil _args)
              -> std::function<T2(
                  std::function<T2(std::shared_ptr<List::list<T1>>)>)> {
            return x;
          },
          [&](const typename List::list<T1>::cons _args)
              -> std::function<T2(
                  std::function<T2(std::shared_ptr<List::list<T1>>)>)> {
            T1 a = _args._a0;
            std::shared_ptr<List::list<T1>> l0 = _args._a1;
            return x0(
                a, l0,
                div_conq_pivot<T1, T2>(le_dec0, x, x0,
                                       split_pivot<T1>(le_dec0, a, l0).first),
                div_conq_pivot<T1, T2>(le_dec0, x, x0,
                                       split_pivot<T1>(le_dec0, a, l0).second));
          }},
      l->v());
}

std::shared_ptr<List::list<unsigned int>>
merge(const std::shared_ptr<List::list<unsigned int>> &l1,
      const std::shared_ptr<List::list<unsigned int>> &l2);

std::shared_ptr<Sig0::sig0<std::shared_ptr<List::list<unsigned int>>>>
qsort(const std::shared_ptr<List::list<unsigned int>> &);
