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

struct WrapperCollisionToken {
  struct Left {
    struct Token {
      static unsigned int id_left(const unsigned int n);
    };
  };

  struct Right {
    struct Token {
      static unsigned int inc_right(const unsigned int n);
    };
  };

  static inline const unsigned int t1 = Left::Token::id_left(((0 + 1) + 1));

  static inline const unsigned int t2 = Right::Token::inc_right(((0 + 1) + 1));
};
