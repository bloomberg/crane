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

template <typename T1>
unsigned int length(const std::shared_ptr<typename List::list<T1>> l) {
  return std::visit(
      Overloaded{
          [&](const typename List::nil<T1> _args) -> unsigned int { return 0; },
          [&](const typename List::cons<T1> _args) -> unsigned int {
            std::shared_ptr<typename List::list<T1>> l_ = _args._a1;
            return (length<T1>(l_) + 1);
          }},
      *l);
}

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

template <typename T1, typename T2,
          MapsTo<std::pair<std::shared_ptr<typename List::list<T1>>,
                           std::shared_ptr<typename List::list<T1>>>,
                 std::shared_ptr<typename List::list<T1>>>
              F0,
          MapsTo<T2, T1> F2,
          MapsTo<T2, std::shared_ptr<typename List::list<T1>>, T2, T2> F3>
T2 div_conq(F0 &&splitF, const T2 x, F2 &&x0, F3 &&x1,
            const std::shared_ptr<typename List::list<T1>> ls) {
  bool s = le_lt_dec(((0 + 1) + 1), length<T1>(ls));
  if (s) {
    return x1(ls, div_conq<T1, T2>(splitF, x, x0, x1, splitF(ls).first),
              div_conq<T1, T2>(splitF, x, x0, x1, splitF(ls).second));
  } else {
    return std::visit(
        Overloaded{
            [&](const typename List::nil<T1> _args)
                -> std::function<T2(
                    std::function<T2(std::shared_ptr<typename List::list<T1>>)>,
                    dummy_prop)> { return x; },
            [&](const typename List::cons<T1> _args)
                -> std::function<T2(
                    std::function<T2(std::shared_ptr<typename List::list<T1>>)>,
                    dummy_prop)> {
              T1 a = _args._a0;
              return x0(a);
            }},
        *ls);
  }
}

template <typename T1>
std::pair<std::shared_ptr<typename List::list<T1>>,
          std::shared_ptr<typename List::list<T1>>>
split(const std::shared_ptr<typename List::list<T1>> ls) {
  return std::visit(
      Overloaded{
          [&](const typename List::nil<T1> _args)
              -> std::pair<std::shared_ptr<typename List::list<T1>>,
                           std::shared_ptr<typename List::list<T1>>> {
            return std::make_pair(List::nil<T1>::make(), List::nil<T1>::make());
          },
          [&](const typename List::cons<T1> _args)
              -> std::pair<std::shared_ptr<typename List::list<T1>>,
                           std::shared_ptr<typename List::list<T1>>> {
            T1 h1 = _args._a0;
            std::shared_ptr<typename List::list<T1>> l = _args._a1;
            return std::visit(
                Overloaded{
                    [&](const typename List::nil<T1> _args)
                        -> std::pair<std::shared_ptr<typename List::list<T1>>,
                                     std::shared_ptr<typename List::list<T1>>> {
                      return std::make_pair(
                          List::cons<T1>::make(h1, List::nil<T1>::make()),
                          List::nil<T1>::make());
                    },
                    [&](const typename List::cons<T1> _args)
                        -> std::pair<std::shared_ptr<typename List::list<T1>>,
                                     std::shared_ptr<typename List::list<T1>>> {
                      T1 h2 = _args._a0;
                      std::shared_ptr<typename List::list<T1>> ls_ = _args._a1;
                      std::shared_ptr<typename List::list<T1>> ls1 =
                          split<T1>(ls_).first;
                      std::shared_ptr<typename List::list<T1>> ls2 =
                          split<T1>(ls_).second;
                      return std::make_pair(List::cons<T1>::make(h1, ls1),
                                            List::cons<T1>::make(h2, ls2));
                    }},
                *l);
          }},
      *ls);
}

template <typename T1, typename T2,
          MapsTo<T2, std::shared_ptr<typename List::list<T1>>, T2, T2> F1,
          MapsTo<T2, T1> F2>
T2 div_conq_split(const T2 x, F1 &&_x0, F2 &&_x1, const T2 _x2) {
  return [&](const std::function<T2(T1)> _x0,
             const std::function<T2(std::shared_ptr<typename List::list<T1>>,
                                    T2, T2)>
                 _x1,
             const std::shared_ptr<typename List::list<T1>> _x2) {
    return div_conq<T1>(split<T1>, _x2, _x0, _x1, _x2);
  }(_x0, _x1, _x2);
}

std::shared_ptr<typename List::list<unsigned int>>
merge(const std::shared_ptr<typename List::list<unsigned int>> l1,
      const std::shared_ptr<typename List::list<unsigned int>> l2);

std::shared_ptr<
    typename Sig0::sig0<std::shared_ptr<typename List::list<unsigned int>>>>
merge_prog(const std::shared_ptr<typename List::list<unsigned int>>,
           const std::shared_ptr<typename List::list<unsigned int>>,
           const std::shared_ptr<typename List::list<unsigned int>>);

std::shared_ptr<
    typename Sig0::sig0<std::shared_ptr<typename List::list<unsigned int>>>>
msort(const std::shared_ptr<typename List::list<unsigned int>>);
