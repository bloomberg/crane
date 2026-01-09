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

std::shared_ptr<
    typename Sig0::sig0<std::shared_ptr<typename List::list<unsigned int>>>>
sort_cons_prog(const unsigned int a,
               const std::shared_ptr<typename List::list<unsigned int>> _x,
               const std::shared_ptr<typename List::list<unsigned int>> l_);

std::shared_ptr<
    typename Sig0::sig0<std::shared_ptr<typename List::list<unsigned int>>>>
isort(const std::shared_ptr<typename List::list<T1>> l);
