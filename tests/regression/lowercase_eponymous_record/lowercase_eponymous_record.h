#ifndef INCLUDED_LOWERCASE_EPONYMOUS_RECORD
#define INCLUDED_LOWERCASE_EPONYMOUS_RECORD

#include <memory>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct LowercaseEponymousRecord {
  struct state {
    unsigned int x;
    unsigned int y;

    std::shared_ptr<State> set_x(const unsigned int n) const {
      return std::make_shared<State>(State{n, this->state::y});
    }
  };

  static inline const std::shared_ptr<State> example =
      std::make_shared<State>(State{0u, 0u})->set_x(42u);
};

#endif // INCLUDED_LOWERCASE_EPONYMOUS_RECORD
