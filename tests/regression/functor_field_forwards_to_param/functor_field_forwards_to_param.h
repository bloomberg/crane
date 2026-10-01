#ifndef INCLUDED_FUNCTOR_FIELD_FORWARDS_TO_PARAM
#define INCLUDED_FUNCTOR_FIELD_FORWARDS_TO_PARAM

#include <concepts>
#include <utility>

template <typename M>
concept MINI = requires {
  typename M::t;
  {
    M::eq_dec(std::declval<typename M::t>(), std::declval<typename M::t>())
  } -> std::same_as<bool>;
};

struct FunctorFieldForwardsToParam {
  struct BoolDec {
    using t = bool;
    static bool eq_dec(bool x, bool y);
  };

  template <MINI M> struct Make {
    using t = typename M::t;

    static bool eq_dec(t x0_, t x1_) {
      return M::eq_dec(std::move(x0_), std::move(x1_));
    }

    static bool eq_dec2(t x0_, t x1_) {
      return eq_dec(std::move(x0_), std::move(x1_));
    }
  };

  using B = Make<BoolDec>;
  static bool go(bool x, bool y);
  static bool go2(bool x, bool y);
};

#endif // INCLUDED_FUNCTOR_FIELD_FORWARDS_TO_PARAM
