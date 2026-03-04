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

struct CtorEscapePrime {
  enum class item { T', T_ };

  template <typename T1>
  static T1 item_rect(const T1 f, const T1 f0, const item i){return [&](void) {
    switch (i) {
 case item::T': {
 return f;
 }
 case item::T_: {
   return f0;
 }
 }
  }();
}

template <typename T1>
static T1 item_rec(const T1 f, const T1 f0, const item i){return [&](void) {
  switch (i) {
 case item::T': {
 return f;
 }
 case item::T_: {
   return f0;
 }
 }
}();
}

static unsigned int tag(const item x);

 static inline const unsigned int t = (tag(item::T') + tag(item::T_));
 }
 ;
