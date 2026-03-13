#ifndef INCLUDED_MUTUAL_MOD
#define INCLUDED_MUTUAL_MOD

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct EvenOdd {
  struct even_list;
  struct odd_list;

  struct even_list {
    // TYPES
    struct ENil {};

    struct ECons {
      unsigned int d_a0;
      std::shared_ptr<odd_list> d_a1;
    };

    using variant_t = std::variant<ENil, ECons>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit even_list(ENil _v) : d_v_(std::move(_v)) {}

    explicit even_list(ECons _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<even_list> ENil_() {
        return std::shared_ptr<even_list>(new even_list(ENil{}));
      }

      static std::shared_ptr<even_list>
      ECons_(unsigned int a0, const std::shared_ptr<odd_list> &a1) {
        return std::shared_ptr<even_list>(new even_list(ECons{a0, a1}));
      }

      static std::unique_ptr<even_list> ENil_uptr() {
        return std::unique_ptr<even_list>(new even_list(ENil{}));
      }

      static std::unique_ptr<even_list>
      ECons_uptr(unsigned int a0, const std::shared_ptr<odd_list> &a1) {
        return std::unique_ptr<even_list>(new even_list(ECons{a0, a1}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  struct odd_list {
    // TYPES
    struct OCons {
      unsigned int d_a0;
      std::shared_ptr<even_list> d_a1;
    };

    using variant_t = std::variant<OCons>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit odd_list(OCons _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<odd_list>
      OCons_(unsigned int a0, const std::shared_ptr<even_list> &a1) {
        return std::shared_ptr<odd_list>(new odd_list(OCons{a0, a1}));
      }

      static std::unique_ptr<odd_list>
      OCons_uptr(unsigned int a0, const std::shared_ptr<even_list> &a1) {
        return std::unique_ptr<odd_list>(new odd_list(OCons{a0, a1}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  __attribute__((pure)) static unsigned int
  even_length(const std::shared_ptr<even_list> &e);
  __attribute__((pure)) static unsigned int
  odd_length(const std::shared_ptr<odd_list> &o);
  static inline const std::shared_ptr<even_list> two = even_list::ctor::ECons_(
      2u, odd_list::ctor::OCons_(1u, even_list::ctor::ENil_()));
  static inline const std::shared_ptr<odd_list> three = odd_list::ctor::OCons_(
      3u, even_list::ctor::ECons_(
              2u, odd_list::ctor::OCons_(1u, even_list::ctor::ENil_())));
};

const unsigned int test_even_len = EvenOdd::even_length(EvenOdd::two);
const unsigned int test_odd_len = EvenOdd::odd_length(EvenOdd::three);

#endif // INCLUDED_MUTUAL_MOD
