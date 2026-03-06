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

struct Bool {
  static bool eqb(const bool b1, const bool b2);
};

template <typename I>
concept EqType = requires(typename I::carrier a0, typename I::carrier a1) {
  typename I::carrier;
  { I::eqb(a1, a0) } -> std::convertible_to<bool>;
};

struct CanonStruct {
  using carrier = std::any;

  struct nat_eqType {
    using carrier = unsigned int;
    static bool eqb(unsigned int a0, unsigned int a1) { return (a0 == a1); }
  };
  static_assert(EqType<nat_eqType>);

  struct bool_eqType {
    using carrier = bool;
    static bool eqb(bool a0, bool a1) { return Bool::eqb(a0, a1); }
  };
  static_assert(EqType<bool_eqType>);

  template <typename _tcI0, typename carrier>
  static bool same(const carrier x, const carrier y) {
    return _tcI0::eqb(x, y);
  }

  static inline const bool test_nat =
      same<nat_eqType>((((0 + 1) + 1) + 1), (((((0 + 1) + 1) + 1) + 1) + 1));

  static inline const bool test_bool = same<bool_eqType>(true, false);
};
