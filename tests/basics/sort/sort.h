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
  unsigned int length() const {
    return std::visit(
        Overloaded{
            [](const typename List<A>::nil _args) -> unsigned int { return 0; },
            [](const typename List<A>::cons _args) -> unsigned int {
              std::shared_ptr<List<A>> l_ = _args._a1;
              return (std::move(l_)->length() + 1);
            }},
        this->v());
  }
};

template <typename A> struct Sig {
public:
  struct exist {
    A _a0;
  };
  using variant_t = std::variant<exist>;

private:
  variant_t v_;
  explicit Sig(exist _v) : v_(std::move(_v)) {}

public:
  struct ctor {
    ctor() = delete;
    static std::shared_ptr<Sig<A>> exist_(A a0) {
      return std::shared_ptr<Sig<A>>(new Sig<A>(exist{a0}));
    }
    static std::unique_ptr<Sig<A>> exist_uptr(A a0) {
      return std::unique_ptr<Sig<A>>(new Sig<A>(exist{a0}));
    }
  };
  const variant_t &v() const { return v_; }
  variant_t &v_mut() { return v_; }
};

struct Compare_dec {
  static bool le_lt_dec(const unsigned int n, const unsigned int m);

  static bool le_gt_dec(const unsigned int _x0, const unsigned int _x1);

  static bool le_dec(const unsigned int n, const unsigned int m);
};

struct Sort {
  template <
      typename T1, typename T2,
      MapsTo<std::pair<std::shared_ptr<List<T1>>, std::shared_ptr<List<T1>>>,
             std::shared_ptr<List<T1>>>
          F0,
      MapsTo<T2, T1> F2, MapsTo<T2, std::shared_ptr<List<T1>>, T2, T2> F3>
  static T2 div_conq(F0 &&splitF, const T2 x, F2 &&x0, F3 &&x1,
                     const std::shared_ptr<List<T1>> &ls) {
    bool s = Compare_dec::le_lt_dec(((0 + 1) + 1), ls->length());
    if (s) {
      return x1(ls, div_conq<T1, T2>(splitF, x, x0, x1, splitF(ls).first),
                div_conq<T1, T2>(splitF, x, x0, x1, splitF(ls).second));
    } else {
      return std::visit(
          Overloaded{
              [&](const typename List<T1>::nil _args) -> auto { return x; },
              [&](const typename List<T1>::cons _args) -> auto {
                T1 a = _args._a0;
                return x0(a);
              }},
          ls->v());
    }
  }

  template <typename T1>
  static std::pair<std::shared_ptr<List<T1>>, std::shared_ptr<List<T1>>>
  split(const std::shared_ptr<List<T1>> &ls) {
    return std::visit(
        Overloaded{
            [](const typename List<T1>::nil _args)
                -> std::pair<std::shared_ptr<List<T1>>,
                             std::shared_ptr<List<T1>>> {
              return std::make_pair(List<T1>::ctor::nil_(),
                                    List<T1>::ctor::nil_());
            },
            [](const typename List<T1>::cons _args)
                -> std::pair<std::shared_ptr<List<T1>>,
                             std::shared_ptr<List<T1>>> {
              T1 h1 = _args._a0;
              std::shared_ptr<List<T1>> l = _args._a1;
              return std::visit(
                  Overloaded{
                      [&](const typename List<T1>::nil _args)
                          -> std::pair<std::shared_ptr<List<T1>>,
                                       std::shared_ptr<List<T1>>> {
                        return std::make_pair(
                            List<T1>::ctor::cons_(h1, List<T1>::ctor::nil_()),
                            List<T1>::ctor::nil_());
                      },
                      [&](const typename List<T1>::cons _args)
                          -> std::pair<std::shared_ptr<List<T1>>,
                                       std::shared_ptr<List<T1>>> {
                        T1 h2 = _args._a0;
                        std::shared_ptr<List<T1>> ls_ = _args._a1;
                        std::shared_ptr<List<T1>> ls1 = split<T1>(ls_).first;
                        std::shared_ptr<List<T1>> ls2 = split<T1>(ls_).second;
                        return std::make_pair(
                            List<T1>::ctor::cons_(h1, ls1),
                            List<T1>::ctor::cons_(h2, std::move(ls2)));
                      }},
                  std::move(l)->v());
            }},
        ls->v());
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F1,
            MapsTo<T2, std::shared_ptr<List<T1>>, T2, T2> F2>
  static T2 div_conq_split(const T2 x, F1 &&_x0, F2 &&_x1,
                           const std::shared_ptr<List<T1>> &_x2) {
    return div_conq<T1, T2>(split<T1>, x, _x0, _x1, _x2);
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F1, MapsTo<T2, T1, T1> F2,
            MapsTo<T2, T1, T1, std::shared_ptr<List<T1>>, T2, T2> F3>
  static T2 div_conq_pair(const T2 x, F1 &&x0, F2 &&x1, F3 &&x2,
                          const std::shared_ptr<List<T1>> &l) {
    return std::visit(
        Overloaded{
            [&](const typename List<T1>::nil _args) -> auto { return x; },
            [&](const typename List<T1>::cons _args) -> auto {
              T1 a = _args._a0;
              std::shared_ptr<List<T1>> l0 = _args._a1;
              return std::visit(
                  Overloaded{[&](const typename List<T1>::nil _args) -> auto {
                               return x0(a);
                             },
                             [&](const typename List<T1>::cons _args) -> auto {
                               T1 a0 = _args._a0;
                               std::shared_ptr<List<T1>> l1 = _args._a1;
                               return x2(
                                   a, a0, l1, x1(a, a0),
                                   div_conq_pair<T1, T2>(x, x0, x1, x2, l1));
                             }},
                  std::move(l0)->v());
            }},
        l->v());
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static std::pair<std::shared_ptr<List<T1>>, std::shared_ptr<List<T1>>>
  split_pivot(F0 &&le_dec0, const T1 pivot,
              const std::shared_ptr<List<T1>> &l) {
    return std::visit(
        Overloaded{[](const typename List<T1>::nil _args)
                       -> std::pair<std::shared_ptr<List<T1>>,
                                    std::shared_ptr<List<T1>>> {
                     return std::make_pair(List<T1>::ctor::nil_(),
                                           List<T1>::ctor::nil_());
                   },
                   [&](const typename List<T1>::cons _args)
                       -> std::pair<std::shared_ptr<List<T1>>,
                                    std::shared_ptr<List<T1>>> {
                     T1 a = _args._a0;
                     std::shared_ptr<List<T1>> l_ = _args._a1;
                     std::shared_ptr<List<T1>> l1 =
                         split_pivot<T1>(le_dec0, pivot, l_).first;
                     std::shared_ptr<List<T1>> l2 =
                         split_pivot<T1>(le_dec0, pivot, l_).second;
                     if (le_dec0(a, pivot)) {
                       return std::make_pair(List<T1>::ctor::cons_(a, l1),
                                             std::move(l2));
                     } else {
                       return std::make_pair(
                           l1, List<T1>::ctor::cons_(a, std::move(l2)));
                     }
                   }},
        l->v());
  }

  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0,
            MapsTo<T2, T1, std::shared_ptr<List<T1>>, T2, T2> F2>
  static T2 div_conq_pivot(F0 &&le_dec0, const T2 x, F2 &&x0,
                           const std::shared_ptr<List<T1>> &l) {
    return std::visit(
        Overloaded{
            [&](const typename List<T1>::nil _args) -> auto { return x; },
            [&](const typename List<T1>::cons _args) -> auto {
              T1 a = _args._a0;
              std::shared_ptr<List<T1>> l0 = _args._a1;
              return x0(
                  a, l0,
                  div_conq_pivot<T1, T2>(le_dec0, x, x0,
                                         split_pivot(le_dec0, a, l0).first),
                  div_conq_pivot<T1, T2>(le_dec0, x, x0,
                                         split_pivot(le_dec0, a, l0).second));
            }},
        l->v());
  }

  static std::shared_ptr<Sig<std::shared_ptr<List<unsigned int>>>>
  sort_cons_prog(const unsigned int a,
                 const std::shared_ptr<List<unsigned int>> &_x,
                 const std::shared_ptr<List<unsigned int>> &l_);

  static std::shared_ptr<Sig<std::shared_ptr<List<unsigned int>>>>
  isort(const std::shared_ptr<List<unsigned int>> &l);

  static std::shared_ptr<List<unsigned int>>
  merge(std::shared_ptr<List<unsigned int>> l1,
        const std::shared_ptr<List<unsigned int>> &l2);

  static std::shared_ptr<Sig<std::shared_ptr<List<unsigned int>>>>
  merge_prog(const std::shared_ptr<List<unsigned int>> &_x,
             std::shared_ptr<List<unsigned int>> l1,
             std::shared_ptr<List<unsigned int>> l2);

  static std::shared_ptr<Sig<std::shared_ptr<List<unsigned int>>>>
  msort(const std::shared_ptr<List<unsigned int>> &);

  static std::shared_ptr<Sig<std::shared_ptr<List<unsigned int>>>>
  pair_merge_prog(const unsigned int _x, const unsigned int _x0,
                  const std::shared_ptr<List<unsigned int>> &_x1,
                  std::shared_ptr<List<unsigned int>> l_,
                  std::shared_ptr<List<unsigned int>> l_0);

  static std::shared_ptr<Sig<std::shared_ptr<List<unsigned int>>>>
  psort(const std::shared_ptr<List<unsigned int>> &);

  static std::shared_ptr<Sig<std::shared_ptr<List<unsigned int>>>>
  qsort(const std::shared_ptr<List<unsigned int>> &);
};
