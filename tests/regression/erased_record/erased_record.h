#ifndef INCLUDED_ERASED_RECORD
#define INCLUDED_ERASED_RECORD

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

struct ErasedRecord {
  struct ManyProps {
    unsigned int field0;
    unsigned int field1;
    unsigned int field2;
    unsigned int field3;
    unsigned int field4;
  };

  __attribute__((pure)) static unsigned int
  complex_match(const std::shared_ptr<ManyProps> &r);
  __attribute__((pure)) static unsigned int
  unusual_body(const std::shared_ptr<ManyProps> &r);

  struct MostlyProps {
    unsigned int real1;
    unsigned int real2;
    unsigned int real3;
  };

  __attribute__((pure)) static unsigned int
  access_mostly_props(const std::shared_ptr<MostlyProps> &r);
  static inline const unsigned int test1 =
      complex_match(std::make_shared<ManyProps>(ManyProps{1u, 2u, 3u, 4u, 5u}));
  static inline const unsigned int test2 =
      unusual_body(std::make_shared<ManyProps>(ManyProps{1u, 2u, 3u, 4u, 5u}));
  static inline const unsigned int test3 = access_mostly_props(
      std::make_shared<MostlyProps>(MostlyProps{5u, 10u, 15u}));
};

#endif // INCLUDED_ERASED_RECORD
