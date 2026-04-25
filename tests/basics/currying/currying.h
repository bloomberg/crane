#ifndef INCLUDED_CURRYING
#define INCLUDED_CURRYING

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
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_shared<T>(x->clone()) : nullptr;
  } else {
    return x;
  }
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

struct Currying {
  __attribute__((pure)) static unsigned int
  add3(const unsigned int &a, const unsigned int &b, const unsigned int &c);
  __attribute__((pure)) static unsigned int
  add3_partial1(const unsigned int &_x0, const unsigned int &_x1);
  __attribute__((pure)) static unsigned int
  add3_partial2(const unsigned int &_x0);

  template <typename t_A, typename t_B> struct pair {
    // TYPES
    struct Pair0 {
      t_A d_a0;
      t_B d_a1;
    };

    using variant_t = std::variant<Pair0>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    pair() {}

    explicit pair(Pair0 _v) : d_v_(std::move(_v)) {}

    pair(const pair<t_A, t_B> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    pair(pair<t_A, t_B> &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) pair<t_A, t_B> &
    operator=(const pair<t_A, t_B> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) pair<t_A, t_B> &operator=(pair<t_A, t_B> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) pair<t_A, t_B> clone() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<Pair0>(_sv.v());
      return pair<t_A, t_B>(
          Pair0{clone_as_value<t_A>(d_a0), clone_as_value<t_B>(d_a1)});
    }

    template <typename _CloneT0, typename _CloneT1>
    __attribute__((pure)) pair<_CloneT0, _CloneT1> clone_as() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<Pair0>(_sv.v());
      return pair<_CloneT0, _CloneT1>(typename pair<_CloneT0, _CloneT1>::Pair0{
          clone_as_value<_CloneT0>(d_a0), clone_as_value<_CloneT1>(d_a1)});
    }

    // CREATORS
    __attribute__((pure)) static pair<t_A, t_B> pair0(t_A a0, t_B a1) {
      return pair(Pair0{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) pair<t_A, t_B> *operator->() { return this; }

    __attribute__((pure)) const pair<t_A, t_B> *operator->() const {
      return this;
    }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = pair<t_A, t_B>(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  static T3 pair_rect(F0 &&f, const pair<T1, T2> &p) {
    const auto &[d_a0, d_a1] = std::get<typename pair<T1, T2>::Pair0>(p.v());
    return f(d_a0, d_a1);
  }

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  static T3 pair_rec(F0 &&f, const pair<T1, T2> &p) {
    const auto &[d_a0, d_a1] = std::get<typename pair<T1, T2>::Pair0>(p.v());
    return f(d_a0, d_a1);
  }

  template <typename T1, typename T2, typename T3, MapsTo<T3, pair<T1, T2>> F0>
  static T3 curry(F0 &&f, const T1 a, const T2 b) {
    return f(pair<T1, T2>::pair0(a, b));
  }

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  static T3 uncurry(F0 &&f, const pair<T1, T2> &p) {
    const auto &[d_a0, d_a1] = std::get<typename pair<T1, T2>::Pair0>(p.v());
    return f(d_a0, d_a1);
  }

  __attribute__((pure)) static unsigned int
  pair_add(const pair<unsigned int, unsigned int> &p);
  __attribute__((pure)) static unsigned int
  curried_add(const unsigned int &_x0, const unsigned int &_x1);
  __attribute__((pure)) static unsigned int
  uncurried_add3(const pair<unsigned int, pair<unsigned int, unsigned int>> &p);

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  static T3 flip(F0 &&f, const T2 b, const T1 a) {
    return f(a, b);
  }

  __attribute__((pure)) static unsigned int sub(const unsigned int &_x0,
                                                const unsigned int &_x1);
  __attribute__((pure)) static unsigned int
  flipped_sub(const unsigned int &_x0, const unsigned int &_x1);
  __attribute__((pure)) static unsigned int add_base(const unsigned int &_x0,
                                                     const unsigned int &_x1);
  __attribute__((pure)) static unsigned int add_ten(const unsigned int &_x0);
  static inline const unsigned int test_add3 = add3(1u, 2u, 3u);
  static inline const unsigned int test_partial1 = add3_partial1(2u, 3u);
  static inline const unsigned int test_partial2 = add3_partial2(3u);
  static inline const unsigned int test_curried = curried_add(3u, 4u);
  static inline const unsigned int test_flip = flipped_sub(3u, 7u);
  static inline const unsigned int test_add_ten = add_ten(5u);
};

#endif // INCLUDED_CURRYING
