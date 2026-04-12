#ifndef INCLUDED_RECORD_APPLY
#define INCLUDED_RECORD_APPLY

#include <functional>
#include <memory>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct RecordApply {
  struct R {
    std::function<unsigned int(unsigned int, unsigned int)> f;
    unsigned int _tag;
  };

  __attribute__((pure)) static unsigned int
  apply_record(const std::shared_ptr<R> &r0, const unsigned int a,
               const unsigned int b);
  static inline const std::shared_ptr<R> r = std::make_shared<R>(
      R{[](const unsigned int x, const unsigned int) { return x; }, 3u});
  static inline const unsigned int three = r->f(3u, 0u);
};

#endif // INCLUDED_RECORD_APPLY
