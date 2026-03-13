#ifndef INCLUDED_SORT
#define INCLUDED_SORT

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

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<t_A>> Nil_() {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::shared_ptr<List<t_A>>
    Cons_(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }

    static std::unique_ptr<List<t_A>> Nil_uptr() {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::unique_ptr<List<t_A>>
    Cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) unsigned int length() const {
    return std::visit(
        Overloaded{[](const typename List<t_A>::Nil _args) -> unsigned int {
                     return 0u;
                   },
                   [](const typename List<t_A>::Cons _args) -> unsigned int {
                     std::shared_ptr<List<t_A>> l_ = _args.d_a1;
                     return (std::move(l_)->length() + 1);
                   }},
        this->v());
  }
};

template <typename t_A> struct Sig {
  // TYPES
  struct Exist {
    t_A d_a0;
  };

  using variant_t = std::variant<Exist>;

private:
  // DATA
  variant_t d_v_;

  // CREATORS
  explicit Sig(Exist _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<Sig<t_A>> Exist_(t_A a0) {
      return std::shared_ptr<Sig<t_A>>(new Sig<t_A>(Exist{a0}));
    }

    static std::unique_ptr<Sig<t_A>> Exist_uptr(t_A a0) {
      return std::unique_ptr<Sig<t_A>>(new Sig<t_A>(Exist{a0}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct Compare_dec {
  __attribute__((pure)) static bool le_lt_dec(const unsigned int n,
                                              const unsigned int m);
  __attribute__((pure)) static bool le_gt_dec(const unsigned int _x0,
                                              const unsigned int _x1);
  __attribute__((pure)) static bool le_dec(const unsigned int n,
                                           const unsigned int m);
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
    bool s = Compare_dec::le_lt_dec(2u, ls->length());
    if (std::move(s)) {
      return x1(ls, div_conq<T1, T2>(splitF, x, x0, x1, splitF(ls).first),
                div_conq<T1, T2>(splitF, x, x0, x1, splitF(ls).second));
    } else {
      return std::visit(
          Overloaded{
              [&](const typename List<T1>::Nil _args) -> auto { return x; },
              [&](const typename List<T1>::Cons _args) -> auto {
                T1 a = _args.d_a0;
                return x0(a);
              }},
          ls->v());
    }
  }

  template <typename T1>
  __attribute__((pure)) static std::pair<std::shared_ptr<List<T1>>,
                                         std::shared_ptr<List<T1>>>
  split(const std::shared_ptr<List<T1>> &ls) {
    return std::visit(
        Overloaded{
            [](const typename List<T1>::Nil _args)
                -> std::pair<std::shared_ptr<List<T1>>,
                             std::shared_ptr<List<T1>>> {
              return std::make_pair(List<T1>::ctor::Nil_(),
                                    List<T1>::ctor::Nil_());
            },
            [](const typename List<T1>::Cons _args)
                -> std::pair<std::shared_ptr<List<T1>>,
                             std::shared_ptr<List<T1>>> {
              T1 h1 = _args.d_a0;
              std::shared_ptr<List<T1>> l = _args.d_a1;
              return std::visit(
                  Overloaded{
                      [&](const typename List<T1>::Nil _args)
                          -> std::pair<std::shared_ptr<List<T1>>,
                                       std::shared_ptr<List<T1>>> {
                        return std::make_pair(
                            List<T1>::ctor::Cons_(h1, List<T1>::ctor::Nil_()),
                            List<T1>::ctor::Nil_());
                      },
                      [&](const typename List<T1>::Cons _args)
                          -> std::pair<std::shared_ptr<List<T1>>,
                                       std::shared_ptr<List<T1>>> {
                        T1 h2 = _args.d_a0;
                        std::shared_ptr<List<T1>> ls_ = _args.d_a1;
                        std::shared_ptr<List<T1>> ls1 = split<T1>(ls_).first;
                        std::shared_ptr<List<T1>> ls2 = split<T1>(ls_).second;
                        return std::make_pair(
                            List<T1>::ctor::Cons_(h1, ls1),
                            List<T1>::ctor::Cons_(h2, std::move(ls2)));
                      }},
                  std::move(l)->v());
            }},
        ls->v());
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F1,
            MapsTo<T2, std::shared_ptr<List<T1>>, T2, T2> F2>
  static T2 div_conq_split(const T2 x, F1 &&_x0, F2 &&_x1,
                           const std::shared_ptr<List<T1>> &_x2) {
    return div_conq(split<T1>, x, _x0, _x1, _x2);
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F1, MapsTo<T2, T1, T1> F2,
            MapsTo<T2, T1, T1, std::shared_ptr<List<T1>>, T2, T2> F3>
  static T2 div_conq_pair(const T2 x, F1 &&x0, F2 &&x1, F3 &&x2,
                          const std::shared_ptr<List<T1>> &l) {
    return std::visit(
        Overloaded{
            [&](const typename List<T1>::Nil _args) -> auto { return x; },
            [&](const typename List<T1>::Cons _args) -> auto {
              T1 a = _args.d_a0;
              std::shared_ptr<List<T1>> l0 = _args.d_a1;
              return std::visit(
                  Overloaded{[&](const typename List<T1>::Nil _args) -> auto {
                               return x0(a);
                             },
                             [&](const typename List<T1>::Cons _args) -> auto {
                               T1 a0 = _args.d_a0;
                               std::shared_ptr<List<T1>> l1 = _args.d_a1;
                               return x2(
                                   a, a0, l1, x1(a, a0),
                                   div_conq_pair<T1, T2>(x, x0, x1, x2, l1));
                             }},
                  std::move(l0)->v());
            }},
        l->v());
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static std::pair<std::shared_ptr<List<T1>>,
                                         std::shared_ptr<List<T1>>>
  split_pivot(F0 &&le_dec0, const T1 pivot,
              const std::shared_ptr<List<T1>> &l) {
    return std::visit(
        Overloaded{[](const typename List<T1>::Nil _args)
                       -> std::pair<std::shared_ptr<List<T1>>,
                                    std::shared_ptr<List<T1>>> {
                     return std::make_pair(List<T1>::ctor::Nil_(),
                                           List<T1>::ctor::Nil_());
                   },
                   [&](const typename List<T1>::Cons _args)
                       -> std::pair<std::shared_ptr<List<T1>>,
                                    std::shared_ptr<List<T1>>> {
                     T1 a = _args.d_a0;
                     std::shared_ptr<List<T1>> l_ = _args.d_a1;
                     std::shared_ptr<List<T1>> l1 =
                         split_pivot<T1>(le_dec0, pivot, l_).first;
                     std::shared_ptr<List<T1>> l2 =
                         split_pivot<T1>(le_dec0, pivot, l_).second;
                     if (le_dec0(a, pivot)) {
                       return std::make_pair(List<T1>::ctor::Cons_(a, l1),
                                             std::move(l2));
                     } else {
                       return std::make_pair(
                           l1, List<T1>::ctor::Cons_(a, std::move(l2)));
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
            [&](const typename List<T1>::Nil _args) -> auto { return x; },
            [&](const typename List<T1>::Cons _args) -> auto {
              T1 a = _args.d_a0;
              std::shared_ptr<List<T1>> l0 = _args.d_a1;
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
  msort(const std::shared_ptr<List<unsigned int>> &_x0);
  static std::shared_ptr<Sig<std::shared_ptr<List<unsigned int>>>>
  pair_merge_prog(const unsigned int _x, const unsigned int _x0,
                  const std::shared_ptr<List<unsigned int>> &_x1,
                  std::shared_ptr<List<unsigned int>> l_,
                  std::shared_ptr<List<unsigned int>> l_0);
  static std::shared_ptr<Sig<std::shared_ptr<List<unsigned int>>>>
  psort(const std::shared_ptr<List<unsigned int>> &_x0);
  static std::shared_ptr<Sig<std::shared_ptr<List<unsigned int>>>>
  qsort(const std::shared_ptr<List<unsigned int>> &_x0);
};

#endif // INCLUDED_SORT
