#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename A> struct List {
public:
  struct nil {};
  struct cons {
    A _a0;
    std::shared_ptr<List<A>> _a1;
  };
  using variant_t = std::variant<nil, cons>;

private:
  variant_t v_;
  explicit List(nil _v) : v_(std::move(_v)) {}
  explicit List(cons _v) : v_(std::move(_v)) {}

public:
  struct ctor {
    ctor() = delete;
    static std::shared_ptr<List<A>> nil_() {
      return std::shared_ptr<List<A>>(new List<A>(nil{}));
    }
    static std::shared_ptr<List<A>> cons_(A a0,
                                          const std::shared_ptr<List<A>> &a1) {
      return std::shared_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
    static std::unique_ptr<List<A>> nil_uptr() {
      return std::unique_ptr<List<A>>(new List<A>(nil{}));
    }
    static std::unique_ptr<List<A>>
    cons_uptr(A a0, const std::shared_ptr<List<A>> &a1) {
      return std::unique_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
  };
  const variant_t &v() const { return v_; }
  variant_t &v_mut() { return v_; }
};

struct Nat {
  static unsigned int sub(const unsigned int n, const unsigned int m);

  static std::pair<unsigned int, unsigned int> divmod(const unsigned int x,
                                                      const unsigned int y,
                                                      const unsigned int q,
                                                      const unsigned int u);

  static unsigned int modulo(const unsigned int x, const unsigned int y);
};

struct WellFoundedRec {
  static std::shared_ptr<List<unsigned int>>
  countdown_acc(const unsigned int n);

  static std::shared_ptr<List<unsigned int>> countdown(const unsigned int);

  static unsigned int div2_wf(const unsigned int x);

  static unsigned int gcd_wf(const unsigned int x, const unsigned int b);

  static inline const unsigned int test_div2_0 = div2_wf(0);

  static inline const unsigned int test_div2_1 = div2_wf((0 + 1));

  static inline const unsigned int test_div2_7 =
      div2_wf((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1));

  static inline const unsigned int test_div2_10 =
      div2_wf(((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1));

  static inline const std::shared_ptr<List<unsigned int>> test_countdown =
      countdown((((((0 + 1) + 1) + 1) + 1) + 1));

  static inline const unsigned int test_gcd_1 = gcd_wf(
      ((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
      ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1));

  static inline const unsigned int test_gcd_2 = gcd_wf(
      (((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                                  1) +
                                 1) +
                                1) +
                               1) +
                              1) +
                             1) +
                            1) +
                           1) +
                          1) +
                         1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1) +
        1) +
       1),
      ((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
         1) +
        1) +
       1));

  static inline const unsigned int test_gcd_3 =
      gcd_wf(0, (((((0 + 1) + 1) + 1) + 1) + 1));
};
