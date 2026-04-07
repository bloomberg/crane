#ifndef INCLUDED_WELL_FOUNDED_REC
#define INCLUDED_WELL_FOUNDED_REC

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

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  static std::unique_ptr<List<t_A>> nil_uptr() {
    return std::make_unique<List<t_A>>(Nil{});
  }

  static std::unique_ptr<List<t_A>>
  cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
    return std::make_unique<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::unique_ptr<List<t_A>> cons_uptr(t_A a0,
                                              std::shared_ptr<List<t_A>> &&a1) {
    return std::make_unique<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct PeanoNat {};

struct WellFoundedRec {
  static std::shared_ptr<List<unsigned int>>
  countdown_acc(const unsigned int n);
  static std::shared_ptr<List<unsigned int>> countdown(const unsigned int _x0);
  __attribute__((pure)) static unsigned int div2_wf(const unsigned int x);
  __attribute__((pure)) static unsigned int gcd_wf(const unsigned int x,
                                                   const unsigned int b);
  static inline const unsigned int test_div2_0 = div2_wf(0u);
  static inline const unsigned int test_div2_1 = div2_wf(1u);
  static inline const unsigned int test_div2_7 = div2_wf(7u);
  static inline const unsigned int test_div2_10 = div2_wf(10u);
  static inline const std::shared_ptr<List<unsigned int>> test_countdown =
      countdown(5u);
  static inline const unsigned int test_gcd_1 = gcd_wf(12u, 8u);
  static inline const unsigned int test_gcd_2 = gcd_wf(35u, 14u);
  static inline const unsigned int test_gcd_3 = gcd_wf(0u, 5u);
};

#endif // INCLUDED_WELL_FOUNDED_REC
