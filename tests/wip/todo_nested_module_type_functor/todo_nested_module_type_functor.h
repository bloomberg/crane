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

template <typename M>
concept OUTER = requires {};

struct TodoNestedModuleTypeFunctor {
  template <OUTER Y> struct Use {
    using Lifted = Y::Make<Y::X>;

    static const typename Lifted::t &test_value() {
      static const typename Lifted::t v = Lifted::zero;
      return v;
    }
  };
};
