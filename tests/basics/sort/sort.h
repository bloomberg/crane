#ifndef INCLUDED_SORT
#define INCLUDED_SORT

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> struct is_shared_ptr : std::false_type {};

template <typename T>
struct is_shared_ptr<std::shared_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  return x ? std::make_unique<T>(x->clone()) : nullptr;
}

template <typename T>
std::shared_ptr<T> clone_value(const std::shared_ptr<T> &x) {
  return x ? std::make_shared<T>(x->clone()) : nullptr;
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using TargetBare = std::remove_cvref_t<Target>;
  using SourceBare = std::remove_cvref_t<Source>;
  if constexpr (is_unique_ptr<TargetBare>::value) {
    using Inner = typename is_unique_ptr<TargetBare>::element_type;
    if constexpr (is_unique_ptr<SourceBare>::value) {
      using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires {
                             typename Inner::crane_element_type;
                             x->template clone_as<
                                 typename Inner::crane_element_type>();
                           }) {
        return std::make_unique<Inner>(
            x->template clone_as<typename Inner::crane_element_type>());
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_unique<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x.clone());
      }
    }
  } else if constexpr (is_shared_ptr<TargetBare>::value) {
    using Inner = typename is_shared_ptr<TargetBare>::element_type;
    if constexpr (is_shared_ptr<SourceBare>::value) {
      using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else if constexpr (is_unique_ptr<SourceBare>::value) {
      if (!x)
        return nullptr;
      if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_shared<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x.clone());
      }
    }
  } else if constexpr (std::is_same_v<TargetBare, SourceBare>) {
    return clone_value(x);
  } else if constexpr (is_unique_ptr<SourceBare>::value) {
    using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (is_shared_ptr<SourceBare>::value) {
    using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (requires {
                         typename TargetBare::crane_element_type;
                         x.template clone_as<
                             typename TargetBare::crane_element_type>();
                       }) {
    return x.template clone_as<typename TargetBare::crane_element_type>();
  } else if constexpr (requires { x.template clone_as<TargetBare>(); }) {
    return x.template clone_as<TargetBare>();
  } else {
    return Target(x);
  }
}

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;
  using crane_element_type = t_A;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  __attribute__((pure)) List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{clone_as_value<t_A>(d_a0),
                            clone_as_value<std::unique_ptr<List<t_A>>>(d_a1)});
    }
  }

  template <typename _CloneT0>
  __attribute__((pure)) List<_CloneT0> clone_as() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<_CloneT0>(typename List<_CloneT0>::Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<_CloneT0>(typename List<_CloneT0>::Cons{
          clone_as_value<_CloneT0>(d_a0),
          clone_as_value<std::unique_ptr<List<_CloneT0>>>(d_a1)});
    }
  }

  // CREATORS
  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1.clone())});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) List<t_A> *operator->() { return this; }

  __attribute__((pure)) const List<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = List<t_A>(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) unsigned int length() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return ((*(d_a1)).length() + 1);
    }
  }
};

template <typename t_A> struct Sig {
  // TYPES
  struct Exist {
    t_A d_x;
  };

  using variant_t = std::variant<Exist>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Sig() {}

  explicit Sig(Exist _v) : d_v_(std::move(_v)) {}

  Sig(const Sig<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Sig(Sig<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  __attribute__((pure)) Sig<t_A> &operator=(const Sig<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) Sig<t_A> &operator=(Sig<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) Sig<t_A> clone() const {
    auto &&_sv = *(this);
    const auto &[d_x] = std::get<Exist>(_sv.v());
    return Sig<t_A>(Exist{clone_as_value<t_A>(d_x)});
  }

  template <typename _CloneT0>
  __attribute__((pure)) Sig<_CloneT0> clone_as() const {
    auto &&_sv = *(this);
    const auto &[d_x] = std::get<Exist>(_sv.v());
    return Sig<_CloneT0>(
        typename Sig<_CloneT0>::Exist{clone_as_value<_CloneT0>(d_x)});
  }

  // CREATORS
  __attribute__((pure)) static Sig<t_A> exist(t_A x) {
    return Sig(Exist{std::move(x)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) Sig<t_A> *operator->() { return this; }

  __attribute__((pure)) const Sig<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = Sig<t_A>(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct Compare_dec {
  __attribute__((pure)) static bool le_lt_dec(const unsigned int &n,
                                              const unsigned int &m);
  __attribute__((pure)) static bool le_gt_dec(const unsigned int &_x0,
                                              const unsigned int &_x1);
  __attribute__((pure)) static bool le_dec(const unsigned int &n,
                                           const unsigned int &m);
};

struct Sort {
  template <typename T1, typename T2,
            MapsTo<std::pair<List<T1>, List<T1>>, List<T1>> F0,
            MapsTo<T2, T1> F2, MapsTo<T2, List<T1>, T2, T2> F3>
  static T2 div_conq(F0 &&splitF, const T2 x, F2 &&x0, F3 &&x1,
                     const List<T1> &ls) {
    bool s = Compare_dec::le_lt_dec(2u, ls.length());
    if (s) {
      return x1(ls, div_conq<T1, T2>(splitF, x, x0, x1, splitF(ls).first),
                div_conq<T1, T2>(splitF, x, x0, x1, splitF(ls).second));
    } else {
      if (std::holds_alternative<typename List<T1>::Nil>(ls.v())) {
        return x;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(ls.v());
        return x0(d_a0);
      }
    }
  }

  template <typename T1>
  __attribute__((pure)) static std::pair<List<T1>, List<T1>>
  split(const List<T1> &ls) {
    if (std::holds_alternative<typename List<T1>::Nil>(ls.v())) {
      return std::make_pair(List<T1>::nil(), List<T1>::nil());
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(ls.v());
      auto &&_sv0 = *(d_a1);
      if (std::holds_alternative<typename List<T1>::Nil>(_sv0.v())) {
        return std::make_pair(List<T1>::cons(d_a0, List<T1>::nil()),
                              List<T1>::nil());
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<T1>::Cons>(_sv0.v());
        auto _cs = split<T1>(*(d_a10));
        const List<T1> &ls1 = _cs.first;
        const List<T1> &ls2 = _cs.second;
        return std::make_pair(List<T1>::cons(d_a0, ls1),
                              List<T1>::cons(d_a00, ls2));
      }
    }
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F1,
            MapsTo<T2, List<T1>, T2, T2> F2>
  static T2 div_conq_split(const T2 x, F1 &&_x0, F2 &&_x1, List<T1> _x2) {
    return div_conq<T1, T2>(split<T1>, x, _x0, _x1, _x2);
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F1, MapsTo<T2, T1, T1> F2,
            MapsTo<T2, T1, T1, List<T1>, T2, T2> F3>
  static T2 div_conq_pair(const T2 x, F1 &&x0, F2 &&x1, F3 &&x2,
                          const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return x;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
      auto &&_sv0 = *(d_a1);
      if (std::holds_alternative<typename List<T1>::Nil>(_sv0.v())) {
        return x0(d_a0);
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<T1>::Cons>(_sv0.v());
        return x2(d_a0, d_a00, *(d_a10), x1(d_a0, d_a00),
                  div_conq_pair<T1, T2>(x, x0, x1, x2, *(d_a10)));
      }
    }
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static std::pair<List<T1>, List<T1>>
  split_pivot(F0 &&le_dec0, const T1 pivot, const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return std::make_pair(List<T1>::nil(), List<T1>::nil());
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
      auto _cs = split_pivot<T1>(le_dec0, pivot, *(d_a1));
      const List<T1> &l1 = _cs.first;
      const List<T1> &l2 = _cs.second;
      if (le_dec0(d_a0, pivot)) {
        return std::make_pair(List<T1>::cons(d_a0, l1), l2);
      } else {
        return std::make_pair(l1, List<T1>::cons(d_a0, l2));
      }
    }
  }

  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0,
            MapsTo<T2, T1, List<T1>, T2, T2> F2>
  static T2 div_conq_pivot(F0 &&le_dec0, const T2 x, F2 &&x0,
                           const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return x;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
      return x0(
          d_a0, *(d_a1),
          div_conq_pivot<T1, T2>(le_dec0, x, x0,
                                 split_pivot(le_dec0, d_a0, *(d_a1)).first),
          div_conq_pivot<T1, T2>(le_dec0, x, x0,
                                 split_pivot(le_dec0, d_a0, *(d_a1)).second));
    }
  }

  __attribute__((pure)) static Sig<List<unsigned int>>
  sort_cons_prog(unsigned int a, const List<unsigned int> &_x,
                 const List<unsigned int> &l_);
  __attribute__((pure)) static Sig<List<unsigned int>>
  isort(const List<unsigned int> &l);
  __attribute__((pure)) static List<unsigned int>
  merge(List<unsigned int> l1, const List<unsigned int> &l2);
  __attribute__((pure)) static Sig<List<unsigned int>>
  merge_prog(const List<unsigned int> &_x, const List<unsigned int> &l1,
             const List<unsigned int> &l2);
  __attribute__((pure)) static Sig<List<unsigned int>>
  msort(const List<unsigned int> &_x0);
  __attribute__((pure)) static Sig<List<unsigned int>>
  pair_merge_prog(const unsigned int &_x, const unsigned int &_x0,
                  const List<unsigned int> &_x1, const List<unsigned int> &l_,
                  const List<unsigned int> &l_0);
  __attribute__((pure)) static Sig<List<unsigned int>>
  psort(const List<unsigned int> &_x0);
  __attribute__((pure)) static Sig<List<unsigned int>>
  qsort(const List<unsigned int> &_x0);
};

#endif // INCLUDED_SORT
