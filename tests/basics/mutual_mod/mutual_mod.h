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

struct EvenOdd {
  struct even_list;
  struct odd_list;
  struct even_list {
  public:
    struct ENil {};
    struct ECons {
      unsigned int _a0;
      std::shared_ptr<odd_list> _a1;
    };
    using variant_t = std::variant<ENil, ECons>;

  private:
    variant_t v_;
    explicit even_list(ENil x) : v_(std::move(x)) {}
    explicit even_list(ECons x) : v_(std::move(x)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<even_list> ENil_() {
        return std::shared_ptr<even_list>(new even_list(ENil{}));
      }
      static std::shared_ptr<even_list>
      ECons_(unsigned int a0, const std::shared_ptr<odd_list> &a1) {
        return std::shared_ptr<even_list>(new even_list(ECons{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
  };
  struct odd_list {
  public:
    struct OCons {
      unsigned int _a0;
      std::shared_ptr<even_list> _a1;
    };
    using variant_t = std::variant<OCons>;

  private:
    variant_t v_;
    explicit odd_list(OCons x) : v_(std::move(x)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<odd_list>
      OCons_(unsigned int a0, const std::shared_ptr<even_list> &a1) {
        return std::shared_ptr<odd_list>(new odd_list(OCons{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
  };

  static unsigned int even_length(const std::shared_ptr<even_list> &e);
  static unsigned int odd_length(const std::shared_ptr<odd_list> &o);

  static inline const std::shared_ptr<even_list> two = even_list::ctor::ECons_(
      ((0 + 1) + 1), odd_list::ctor::OCons_((0 + 1), even_list::ctor::ENil_()));

  static inline const std::shared_ptr<odd_list> three = odd_list::ctor::OCons_(
      (((0 + 1) + 1) + 1),
      even_list::ctor::ECons_(
          ((0 + 1) + 1),
          odd_list::ctor::OCons_((0 + 1), even_list::ctor::ENil_())));
};

const unsigned int test_even_len = EvenOdd::even_length(EvenOdd::two);

const unsigned int test_odd_len = EvenOdd::odd_length(EvenOdd::three);
