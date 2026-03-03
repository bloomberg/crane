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

struct Nat {
  static std::pair<unsigned int, unsigned int> divmod(const unsigned int x,
                                                      const unsigned int y,
                                                      const unsigned int q,
                                                      const unsigned int u);

  static unsigned int div(const unsigned int x, const unsigned int y);
};

struct SPropTest {
  template <typename T1>
  static inline const T1 sFalse_rect =
      [](void) { throw std::logic_error("absurd case"); }();

  template <typename T1>
  static inline const T1 sFalse_rec =
      [](void) { throw std::logic_error("absurd case"); }();

  template <typename A> struct Box {
    A box_value;
  };

  template <typename T1>
  static T1 box_value(const std::shared_ptr<Box<T1>> &b) {
    return b->box_value;
  }

  static unsigned int guarded_pred(const unsigned int n);

  static unsigned int safe_div(const unsigned int, const unsigned int);

  static inline const unsigned int test_guarded =
      guarded_pred((((((0 + 1) + 1) + 1) + 1) + 1));

  static inline const unsigned int test_box =
      ((((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) +
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
                1) +
               1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1) +
        1) +
       1);

  static inline const unsigned int test_div =
      safe_div(((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
               (((0 + 1) + 1) + 1));
};
