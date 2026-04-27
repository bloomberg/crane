#ifndef INCLUDED_MUTUAL_MOD
#define INCLUDED_MUTUAL_MOD

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

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

    even_list &operator=(const even_list &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    even_list &operator=(even_list &&_other) {
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
        return even_list(ECons{
            d_a0, d_a1 ? std::make_unique<EvenOdd::odd_list>(d_a1->clone())
                       : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static even_list enil() { return even_list(ENil{}); }

    __attribute__((pure)) static even_list econs(unsigned int a0,
                                                 const odd_list &a1) {
      return even_list(ECons{std::move(a0), std::make_unique<odd_list>(a1)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

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

    odd_list &operator=(const odd_list &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    odd_list &operator=(odd_list &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) odd_list clone() const {
      auto &&_sv = *(this);
      const auto &[d_a0, d_a1] = std::get<OCons>(_sv.v());
      return odd_list(
          OCons{d_a0, d_a1 ? std::make_unique<EvenOdd::even_list>(d_a1->clone())
                           : nullptr});
    }

    // CREATORS
    __attribute__((pure)) static odd_list ocons(unsigned int a0,
                                                const even_list &a1) {
      return odd_list(OCons{std::move(a0), std::make_unique<even_list>(a1)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

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
