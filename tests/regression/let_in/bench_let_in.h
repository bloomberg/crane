#ifndef INCLUDED_BENCH_LET_IN
#define INCLUDED_BENCH_LET_IN

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

struct BenchLetIn {
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

    template <typename T1, MapsTo<T1, t_A, t_B> F0> T1 pair_rec(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] =
          std::get<typename pair<t_A, t_B>::Pair0>(_sv.v());
      return f(d_a0, d_a1);
    }

    template <typename T1, MapsTo<T1, t_A, t_B> F0> T1 pair_rect(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] =
          std::get<typename pair<t_A, t_B>::Pair0>(_sv.v());
      return f(d_a0, d_a1);
    }
  };

  __attribute__((pure)) static unsigned int swap_snd(unsigned int a,
                                                     unsigned int b);
  __attribute__((pure)) static unsigned int add_via_pair(unsigned int a,
                                                         unsigned int b);
  __attribute__((pure)) static unsigned int
  nested_swap(unsigned int a, unsigned int b, unsigned int c, unsigned int d);
  __attribute__((pure)) static unsigned int sum_via_pairs(unsigned int n);

  template <typename t_A, typename t_B, typename t_C> struct triple {
    // TYPES
    struct Triple0 {
      t_A d_a0;
      t_B d_a1;
      t_C d_a2;
    };

    using variant_t = std::variant<Triple0>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    triple() {}

    explicit triple(Triple0 _v) : d_v_(std::move(_v)) {}

    triple(const triple<t_A, t_B, t_C> &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    triple(triple<t_A, t_B, t_C> &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) triple<t_A, t_B, t_C> &
    operator=(const triple<t_A, t_B, t_C> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) triple<t_A, t_B, t_C> &
    operator=(triple<t_A, t_B, t_C> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) triple<t_A, t_B, t_C> clone() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1, d_a2] = std::get<Triple0>(_sv.v());
      return triple<t_A, t_B, t_C>(Triple0{clone_as_value<t_A>(d_a0),
                                           clone_as_value<t_B>(d_a1),
                                           clone_as_value<t_C>(d_a2)});
    }

    template <typename _CloneT0, typename _CloneT1, typename _CloneT2>
    __attribute__((pure)) triple<_CloneT0, _CloneT1, _CloneT2>
    clone_as() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1, d_a2] = std::get<Triple0>(_sv.v());
      return triple<_CloneT0, _CloneT1, _CloneT2>(
          typename triple<_CloneT0, _CloneT1, _CloneT2>::Triple0{
              clone_as_value<_CloneT0>(d_a0), clone_as_value<_CloneT1>(d_a1),
              clone_as_value<_CloneT2>(d_a2)});
    }

    // CREATORS
    __attribute__((pure)) static triple<t_A, t_B, t_C> triple0(t_A a0, t_B a1,
                                                               t_C a2) {
      return triple(Triple0{std::move(a0), std::move(a1), std::move(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) triple<t_A, t_B, t_C> *operator->() { return this; }

    __attribute__((pure)) const triple<t_A, t_B, t_C> *operator->() const {
      return this;
    }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = triple<t_A, t_B, t_C>(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1, MapsTo<T1, t_A, t_B, t_C> F0>
    T1 triple_rec(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename triple<t_A, t_B, t_C>::Triple0>(_sv.v());
      return f(d_a0, d_a1, d_a2);
    }

    template <typename T1, MapsTo<T1, t_A, t_B, t_C> F0>
    T1 triple_rect(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename triple<t_A, t_B, t_C>::Triple0>(_sv.v());
      return f(d_a0, d_a1, d_a2);
    }
  };

  __attribute__((pure)) static unsigned int mid3(unsigned int a, unsigned int b,
                                                 unsigned int c);
  __attribute__((pure)) static unsigned int sum3(unsigned int a, unsigned int b,
                                                 unsigned int c);
  __attribute__((pure)) static unsigned int
  chain_pairs(unsigned int a, unsigned int b, unsigned int c);
  static inline const unsigned int test_swap = swap_snd(3u, 4u);
  static inline const unsigned int test_add = add_via_pair(3u, 4u);
  static inline const unsigned int test_nested = nested_swap(1u, 2u, 3u, 4u);
  static inline const unsigned int test_sum_pairs = sum_via_pairs(5u);
  static inline const unsigned int test_mid3 = mid3(1u, 2u, 3u);
  static inline const unsigned int test_sum3 = sum3(1u, 2u, 3u);
  static inline const unsigned int test_chain = chain_pairs(1u, 2u, 3u);
};

#endif // INCLUDED_BENCH_LET_IN
