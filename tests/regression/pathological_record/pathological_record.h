#ifndef INCLUDED_PATHOLOGICAL_RECORD
#define INCLUDED_PATHOLOGICAL_RECORD

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

struct PathologicalRecord {
  struct Rec {
    unsigned int f1;
    unsigned int f2;
    unsigned int f3;
  };

  __attribute__((pure)) static unsigned int
  hof_access(const std::shared_ptr<Rec> &r);
  __attribute__((pure)) static unsigned int
  nested_lets(const std::shared_ptr<Rec> &r);
  __attribute__((pure)) static unsigned int
  conditional_access(const std::shared_ptr<Rec> &r, const bool flag);
  __attribute__((pure)) static unsigned int
  countdown(const unsigned int n, const std::shared_ptr<Rec> &r);
  __attribute__((pure)) static unsigned int
  double_match(const std::shared_ptr<Rec> &r1, const std::shared_ptr<Rec> &r2);
  __attribute__((pure)) static unsigned int
  closure_over_fields(const std::shared_ptr<Rec> &r, const unsigned int x);
  static inline const unsigned int use_closure =
      closure_over_fields(std::make_shared<Rec>(Rec{1u, 2u, 3u}), 10u);
  __attribute__((pure)) static unsigned int
  guarded_pattern(const std::shared_ptr<Rec> &r);

  struct BigRec {
    unsigned int bf1;
    unsigned int bf2;
    unsigned int bf3;
    unsigned int bf4;
    unsigned int bf5;
  };

  __attribute__((pure)) static unsigned int
  scrambled_access(const std::shared_ptr<BigRec> &r);
  __attribute__((pure)) static unsigned int
  repeated_access(const std::shared_ptr<BigRec> &r);
  static inline const unsigned int test1 =
      hof_access(std::make_shared<Rec>(Rec{1u, 2u, 3u}));
  static inline const unsigned int test2 =
      nested_lets(std::make_shared<Rec>(Rec{4u, 5u, 6u}));
  static inline const unsigned int test3 =
      double_match(std::make_shared<Rec>(Rec{1u, 2u, 3u}),
                   std::make_shared<Rec>(Rec{4u, 5u, 6u}));
};

#endif // INCLUDED_PATHOLOGICAL_RECORD
