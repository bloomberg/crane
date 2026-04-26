#ifndef INCLUDED_MUTUAL_MOD
#define INCLUDED_MUTUAL_MOD

#include <memory>
#include <optional>
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

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_unique<T>(x->clone()) : nullptr;
  } else {
    return x ? std::make_unique<T>(*x) : nullptr;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using T = std::remove_cvref_t<Target>;
  using S = std::remove_cvref_t<Source>;
  if constexpr (requires(const S &s) {
                  s.has_value();
                  *s;
                }) {
    if (!x.has_value())
      return T{};
    using TInner = std::remove_cvref_t<decltype(*std::declval<const T &>())>;
    return T{clone_as_value<TInner>(*x)};
  } else if constexpr (std::is_same_v<T, S>) {
    if constexpr (is_unique_ptr<T>::value) {
      return clone_value(x);
    } else if constexpr (requires { x.clone(); }) {
      return x.clone();
    } else {
      return x;
    }
  } else if constexpr (is_unique_ptr<S>::value) {
    if (!x)
      return T{};
    return clone_as_value<T>(*x);
  } else if constexpr (is_unique_ptr<T>::value) {
    using Inner = typename is_unique_ptr<T>::element_type;
    return std::make_unique<Inner>(clone_as_value<Inner>(x));
  } else {
    return T(x);
  }
}

struct EvenOdd {
  struct even_list;
  struct odd_list;

  struct even_list {
    // TYPES
    struct ENil {};

    struct ECons {
      unsigned int d_a0;
      std::unique_ptr<odd_list> d_a1;
    };

    using variant_t = std::variant<ENil, ECons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    even_list() {}

    explicit even_list(ENil _v) : d_v_(_v) {}

    explicit even_list(ECons _v) : d_v_(std::move(_v)) {}

    even_list(const even_list &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    even_list(even_list &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) even_list &operator=(const even_list &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) even_list &operator=(even_list &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) even_list clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<ENil>(_sv.v())) {
        return even_list(ENil{});
      } else {
        const auto &[d_a0, d_a1] = std::get<ECons>(_sv.v());
        return even_list(ECons{d_a0, clone_value(d_a1)});
      }
    }

    // CREATORS
    __attribute__((pure)) static even_list enil() { return even_list(ENil{}); }

    __attribute__((pure)) static even_list econs(unsigned int a0,
                                                 const odd_list &a1) {
      return even_list(ECons{std::move(a0), std::make_unique<odd_list>(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) even_list *operator->() { return this; }

    __attribute__((pure)) const even_list *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = even_list(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  struct odd_list {
    // TYPES
    struct OCons {
      unsigned int d_a0;
      std::unique_ptr<even_list> d_a1;
    };

    using variant_t = std::variant<OCons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    odd_list() {}

    explicit odd_list(OCons _v) : d_v_(std::move(_v)) {}

    odd_list(const odd_list &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    odd_list(odd_list &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) odd_list &operator=(const odd_list &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) odd_list &operator=(odd_list &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) odd_list clone() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<OCons>(_sv.v());
      return odd_list(OCons{d_a0, clone_value(d_a1)});
    }

    // CREATORS
    __attribute__((pure)) static odd_list ocons(unsigned int a0,
                                                const even_list &a1) {
      return odd_list(OCons{std::move(a0), std::make_unique<even_list>(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) odd_list *operator->() { return this; }

    __attribute__((pure)) const odd_list *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = odd_list(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  __attribute__((pure)) static unsigned int even_length(const even_list &e);
  __attribute__((pure)) static unsigned int odd_length(const odd_list &o);
  static inline const even_list two =
      even_list::econs(2u, odd_list::ocons(1u, even_list::enil()));
  static inline const odd_list three = odd_list::ocons(
      3u, even_list::econs(2u, odd_list::ocons(1u, even_list::enil())));
};

const unsigned int test_even_len = EvenOdd::even_length(EvenOdd::two);
const unsigned int test_odd_len = EvenOdd::odd_length(EvenOdd::three);

#endif // INCLUDED_MUTUAL_MOD
