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
    explicit list(nil x) : v_(std::move(x)) {}
    explicit list(cons x) : v_(std::move(x)) {}

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
    unsigned int length() const {
      return std::visit(
          Overloaded{
              [&](const typename List::list<A>::nil _args) -> unsigned int {
                return 0;
              },
              [&](const typename List::list<A>::cons _args) -> unsigned int {
                std::shared_ptr<List::list<A>> l_ = _args._a1;
                return (l_->length() + 1);
              }},
          this->v());
    }
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
    explicit sig0(exist x) : v_(std::move(x)) {}

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

template <typename T1, typename T2,
          MapsTo<std::pair<std::shared_ptr<List::list<T1>>,
                           std::shared_ptr<List::list<T1>>>,
                 std::shared_ptr<List::list<T1>>>
              F0,
          MapsTo<T2, T1> F2,
          MapsTo<T2, std::shared_ptr<List::list<T1>>, T2, T2> F3>
T2 div_conq(F0 &&splitF, const T2 x, F2 &&x0, F3 &&x1,
            const std::shared_ptr<List::list<T1>> &ls) {
  bool s = le_lt_dec(((0 + 1) + 1), ls->length());
  if (s) {
    return x1(ls, div_conq<T1, T2>(splitF, x, x0, x1, splitF(ls).first),
              div_conq<T1, T2>(splitF, x, x0, x1, splitF(ls).second));
  } else {
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
              return x0(a);
            }},
        ls->v());
  }
}

template <typename T1>
std::pair<std::shared_ptr<List::list<T1>>, std::shared_ptr<List::list<T1>>>
split(const std::shared_ptr<List::list<T1>> &ls) {
  return std::visit(
      Overloaded{[&](const typename List::list<T1>::nil _args)
                     -> std::pair<std::shared_ptr<List::list<T1>>,
                                  std::shared_ptr<List::list<T1>>> {
                   return std::make_pair(List::list<T1>::ctor::nil_(),
                                         List::list<T1>::ctor::nil_());
                 },
                 [&](const typename List::list<T1>::cons _args)
                     -> std::pair<std::shared_ptr<List::list<T1>>,
                                  std::shared_ptr<List::list<T1>>> {
                   T1 h1 = _args._a0;
                   std::shared_ptr<List::list<T1>> l = _args._a1;
                   return std::visit(
                       Overloaded{
                           [&](const typename List::list<T1>::nil _args)
                               -> std::pair<std::shared_ptr<List::list<T1>>,
                                            std::shared_ptr<List::list<T1>>> {
                             return std::make_pair(
                                 List::list<T1>::ctor::cons_(
                                     h1, List::list<T1>::ctor::nil_()),
                                 List::list<T1>::ctor::nil_());
                           },
                           [&](const typename List::list<T1>::cons _args)
                               -> std::pair<std::shared_ptr<List::list<T1>>,
                                            std::shared_ptr<List::list<T1>>> {
                             T1 h2 = _args._a0;
                             std::shared_ptr<List::list<T1>> ls_ = _args._a1;
                             std::shared_ptr<List::list<T1>> ls1 =
                                 split<T1>(ls_).first;
                             std::shared_ptr<List::list<T1>> ls2 =
                                 split<T1>(ls_).second;
                             return std::make_pair(
                                 List::list<T1>::ctor::cons_(h1, ls1),
                                 List::list<T1>::ctor::cons_(h2, ls2));
                           }},
                       l->v());
                 }},
      ls->v());
}

template <typename T1, typename T2,
          MapsTo<T2, std::shared_ptr<List::list<T1>>, T2, T2> F2,
          MapsTo<T2, T1> F3>
T2 div_conq_split(const T2 x, const std::shared_ptr<List::list<T1>> &_x0,
                  F2 &&_x1, F3 &&_x2) {
  return
      [&](const std::function<T2(T1)> _x0,
          const std::function<T2(std::shared_ptr<List::list<T1>>, T2, T2)> _x1,
          const std::shared_ptr<List::list<T1>> _x2) {
        return div_conq<T1>(split<T1>, x, _x0, _x1, _x2);
      }(_x0, _x1, _x2);
}

std::shared_ptr<List::list<unsigned int>>
merge(const std::shared_ptr<List::list<unsigned int>> &l1,
      const std::shared_ptr<List::list<unsigned int>> &l2);

std::shared_ptr<Sig0::sig0<std::shared_ptr<List::list<unsigned int>>>>
merge_prog(const std::shared_ptr<List::list<unsigned int>> &,
           const std::shared_ptr<List::list<unsigned int>> &,
           const std::shared_ptr<List::list<unsigned int>> &);

std::shared_ptr<Sig0::sig0<std::shared_ptr<List::list<unsigned int>>>>
msort(const std::shared_ptr<List::list<unsigned int>> &);
