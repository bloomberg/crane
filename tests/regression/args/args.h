#include <algorithm>
#include <any>
#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct Args {
  struct R {
    std::function<unsigned int(unsigned int, unsigned int)> f;
    unsigned int _tag;
  };

  static unsigned int f(const std::shared_ptr<R> &, const unsigned int,
                        const unsigned int);

  static unsigned int _tag(const std::shared_ptr<R> &r);

  static unsigned int apply_record(const std::shared_ptr<R> &r,
                                   const unsigned int a, const unsigned int b);

  static inline const std::shared_ptr<R> r = std::make_shared<R>(
      R{[](unsigned int x, unsigned int _x) { return x; }, 3u});

  static inline const unsigned int three = r->f(3u, 0u);
};
