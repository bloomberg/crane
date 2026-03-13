#ifndef INCLUDED_RECORD_MATCH
#define INCLUDED_RECORD_MATCH

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

struct RecordMatch {
  struct MyRec {
    unsigned int f1;
    unsigned int f2;
    unsigned int f3;
  };

  __attribute__((pure)) static unsigned int
  sum(const std::shared_ptr<MyRec> &r);
};

#endif // INCLUDED_RECORD_MATCH
