#include <algorithm>
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
  template <typename A> struct nil;
  template <typename A> struct cons;
  template <typename A> using list = std::variant<nil<A>, cons<A>>;
  template <typename A> struct nil {
    static std::shared_ptr<list<A>> make() {
      return std::make_shared<list<A>>(nil<A>{});
    }
  };
  template <typename A> struct cons {
    A _a0;
    std::shared_ptr<list<A>> _a1;
    static std::shared_ptr<list<A>> make(A _a0, std::shared_ptr<list<A>> _a1) {
      return std::make_shared<list<A>>(cons<A>{_a0, _a1});
    }
  };
};

struct Sig0 {
  template <typename A> struct exist;
  template <typename A> using sig0 = std::variant<exist<A>>;
  template <typename A> struct exist {
    A _a0;
    static std::shared_ptr<sig0<A>> make(A _a0) {
      return std::make_shared<sig0<A>>(exist<A>{_a0});
    }
  };
};

bool le_lt_dec(const unsigned int n, const unsigned int m);

bool le_gt_dec(const unsigned int, const unsigned int);

bool le_dec(const unsigned int n, const unsigned int m);

template <typename T1, MapsTo<bool, T1, T1> F0>
std::pair<std::shared_ptr<typename List::list<T1>>,
          std::shared_ptr<typename List::list<T1>>>
split_pivot(F0 &&le_dec0, const T1 pivot,
            const std::shared_ptr<typename List::list<T1>> l) {
  return std::visit(
      Overloaded{[&](const typename List::nil<T1> _args)
                     -> std::pair<std::shared_ptr<typename List::list<T1>>,
                                  std::shared_ptr<typename List::list<T1>>> {
                   return std::make_pair(List::nil<T1>::make(),
                                         List::nil<T1>::make());
                 },
                 [&](const typename List::cons<T1> _args)
                     -> std::pair<std::shared_ptr<typename List::list<T1>>,
                                  std::shared_ptr<typename List::list<T1>>> {
                   T1 a = _args._a0;
                   std::shared_ptr<typename List::list<T1>> l_ = _args._a1;
                   std::shared_ptr<typename List::list<T1>> l1 =
                       split_pivot<T1>(le_dec0, pivot, l_).first;
                   std::shared_ptr<typename List::list<T1>> l2 =
                       split_pivot<T1>(le_dec0, pivot, l_).second;
                   if (le_dec0(a, pivot)) {
                     return std::make_pair(List::cons<T1>::make(a, l1), l2);
                   } else {
                     return std::make_pair(l1, List::cons<T1>::make(a, l2));
                   }
                 }},
      *l);
}

template <typename T1, typename T2, MapsTo<bool, T1, T1> F0,
          MapsTo<T2, T1, std::shared_ptr<typename List::list<T1>>, T2, T2> F2>
T2 div_conq_pivot(F0 &&le_dec0, const T2 x, F2 &&x0,
                  const std::shared_ptr<typename List::list<T1>> l) {
  return std::visit(
      Overloaded{
          [&](const typename List::nil<T1> _args)
              -> std::function<T2(
                  std::function<T2(
                      std::shared_ptr<typename List::list<T1>>)>)> {
            return x;
          },
          [&](const typename List::cons<T1> _args)
              -> std::function<T2(
                  std::function<T2(
                      std::shared_ptr<typename List::list<T1>>)>)> {
            T1 a = _args._a0;
            std::shared_ptr<typename List::list<T1>> l0 = _args._a1;
            return x0(
                a, l0,
                div_conq_pivot<T1, T2>(le_dec0, x, x0,
                                       split_pivot<T1>(le_dec0, a, l0).first),
                div_conq_pivot<T1, T2>(le_dec0, x, x0,
                                       split_pivot<T1>(le_dec0, a, l0).second));
          }},
      *l);
}

std::shared_ptr<typename List::list<unsigned int>>
merge(const std::shared_ptr<typename List::list<unsigned int>> l1,
      const std::shared_ptr<typename List::list<unsigned int>> l2);

std::shared_ptr<
    typename Sig0::sig0<std::shared_ptr<typename List::list<unsigned int>>>>
qsort(const std::shared_ptr<typename List::list<unsigned int>>);
