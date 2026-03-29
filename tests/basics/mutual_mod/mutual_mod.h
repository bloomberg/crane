#ifndef INCLUDED_MUTUAL_MOD
#define INCLUDED_MUTUAL_MOD

#include <memory>
#include <type_traits>
#include <utility>
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

  public:
    // CREATORS
    explicit even_list(ENil _v) : d_v_(std::move(_v)) {}

    explicit even_list(ECons _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<even_list> enil() {
      return std::make_shared<even_list>(ENil{});
    }

    static std::shared_ptr<even_list>
    econs(unsigned int a0, const std::shared_ptr<odd_list> &a1) {
      return std::make_shared<even_list>(ECons{std::move(a0), a1});
    }

    static std::shared_ptr<even_list> econs(unsigned int a0,
                                            std::shared_ptr<odd_list> &&a1) {
      return std::make_shared<even_list>(ECons{std::move(a0), std::move(a1)});
    }

    static std::unique_ptr<even_list> enil_uptr() {
      return std::make_unique<even_list>(ENil{});
    }

    static std::unique_ptr<even_list>
    econs_uptr(unsigned int a0, const std::shared_ptr<odd_list> &a1) {
      return std::make_unique<even_list>(ECons{std::move(a0), a1});
    }

    static std::unique_ptr<even_list>
    econs_uptr(unsigned int a0, std::shared_ptr<odd_list> &&a1) {
      return std::make_unique<even_list>(ECons{std::move(a0), std::move(a1)});
    }

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

  public:
    // CREATORS
    explicit odd_list(OCons _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<odd_list>
    ocons(unsigned int a0, const std::shared_ptr<even_list> &a1) {
      return std::make_shared<odd_list>(OCons{std::move(a0), a1});
    }

    static std::shared_ptr<odd_list> ocons(unsigned int a0,
                                           std::shared_ptr<even_list> &&a1) {
      return std::make_shared<odd_list>(OCons{std::move(a0), std::move(a1)});
    }

    static std::unique_ptr<odd_list>
    ocons_uptr(unsigned int a0, const std::shared_ptr<even_list> &a1) {
      return std::make_unique<odd_list>(OCons{std::move(a0), a1});
    }

    static std::unique_ptr<odd_list>
    ocons_uptr(unsigned int a0, std::shared_ptr<even_list> &&a1) {
      return std::make_unique<odd_list>(OCons{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  __attribute__((pure)) static unsigned int
  even_length(const std::shared_ptr<even_list> &e);
  __attribute__((pure)) static unsigned int
  odd_length(const std::shared_ptr<odd_list> &o);
  static inline const std::shared_ptr<even_list> two =
      even_list::econs(2u, odd_list::ocons(1u, even_list::enil()));
  static inline const std::shared_ptr<odd_list> three = odd_list::ocons(
      3u, even_list::econs(2u, odd_list::ocons(1u, even_list::enil())));
};

const unsigned int test_even_len = EvenOdd::even_length(EvenOdd::two);
const unsigned int test_odd_len = EvenOdd::odd_length(EvenOdd::three);

#endif // INCLUDED_MUTUAL_MOD
