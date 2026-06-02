#ifndef INCLUDED_MUTUAL_MOD
#define INCLUDED_MUTUAL_MOD

#include <memory>
#include <utility>
#include <variant>

struct EvenOdd {
  struct even_list;
  struct odd_list;

  struct even_list {
    // TYPES
    struct ENil {};

    struct ECons {
      uint64_t a0;
      std::shared_ptr<odd_list> a1;
    };

    using variant_t = std::variant<ENil, ECons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    even_list() {}

    explicit even_list(ENil _v) : v_(_v) {}

    explicit even_list(ECons _v) : v_(std::move(_v)) {}

    static even_list enil() { return even_list(ENil{}); }

    static even_list econs(uint64_t a0, odd_list a1) {
      return even_list(ECons{a0, std::make_shared<odd_list>(std::move(a1))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  struct odd_list {
    // TYPES
    struct OCons {
      uint64_t a0;
      std::shared_ptr<even_list> a1;
    };

    using variant_t = std::variant<OCons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    odd_list() {}

    explicit odd_list(OCons _v) : v_(std::move(_v)) {}

    static odd_list ocons(uint64_t a0, even_list a1) {
      return odd_list(OCons{a0, std::make_shared<even_list>(std::move(a1))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  static uint64_t even_length(const even_list &e);
  static uint64_t odd_length(const odd_list &o);
  static inline const even_list two = even_list::econs(
      UINT64_C(2), odd_list::ocons(UINT64_C(1), even_list::enil()));
  static inline const odd_list three = odd_list::ocons(
      UINT64_C(3),
      even_list::econs(UINT64_C(2),
                       odd_list::ocons(UINT64_C(1), even_list::enil())));
};

const uint64_t test_even_len = EvenOdd::even_length(EvenOdd::two);
const uint64_t test_odd_len = EvenOdd::odd_length(EvenOdd::three);

#endif // INCLUDED_MUTUAL_MOD
