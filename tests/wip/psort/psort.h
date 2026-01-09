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

template <
    typename T1, typename T2, MapsTo<T2, T1> F1, MapsTo<T2, T1, T1> F2,
    MapsTo<T2, T1, T1, std::shared_ptr<typename List::list<T1>>, T2, T2> F3>
T2 div_conq_pair(const T2 x, F1 &&x0, F2 &&x1, F3 &&x2,
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
            return std::visit(
                Overloaded{
                    [&](const typename List::nil<T1> _args)
                        -> std::function<T2(
                            std::function<T2(
                                std::shared_ptr<typename List::list<T1>>)>)> {
                      return x0(a);
                    },
                    [&](const typename List::cons<T1> _args)
                        -> std::function<T2(
                            std::function<T2(
                                std::shared_ptr<typename List::list<T1>>)>)> {
                      T1 a0 = _args._a0;
                      std::shared_ptr<typename List::list<T1>> l1 = _args._a1;
                      return x2(a, a0, l1, x1(a, a0),
                                div_conq_pair<T1, T2>(x, x0, x1, x2, l1));
                    }},
                *l0);
          }},
      *l);
}

std::shared_ptr<typename List::list<unsigned int>>
merge(const std::shared_ptr<typename List::list<unsigned int>> l1,
      const std::shared_ptr<typename List::list<unsigned int>> l2);

std::shared_ptr<
    typename Sig0::sig0<std::shared_ptr<typename List::list<unsigned int>>>>
pair_merge_prog(const unsigned int _x, const unsigned int _x0,
                const std::shared_ptr<typename List::list<unsigned int>> _x1,
                const std::shared_ptr<typename List::list<unsigned int>> l_,
                const std::shared_ptr<typename List::list<unsigned int>> l_0);

std::shared_ptr<
    typename Sig0::sig0<std::shared_ptr<typename List::list<unsigned int>>>>
psort(const std::shared_ptr<typename List::list<unsigned int>>);
