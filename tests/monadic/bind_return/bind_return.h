#include <algorithm>
#include <any>
#include <cassert>
#include <fstream>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

enum class unit { tt };

struct List {
  template <typename A> struct list {
  public:
    struct nil {};
    struct cons {
      A _a0;
      std::shared_ptr<List::list<A>> _a1;
    };
    using variant_t = std::variant<nil, cons>;

  private:
    variant_t v_;
    explicit list(nil _v) : v_(std::move(_v)) {}
    explicit list(cons _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<List::list<A>> nil_() {
        return std::shared_ptr<List::list<A>>(new List::list<A>(nil{}));
      }
      static std::shared_ptr<List::list<A>>
      cons_(A a0, const std::shared_ptr<List::list<A>> &a1) {
        return std::shared_ptr<List::list<A>>(new List::list<A>(cons{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
  };
};

struct bindreturn {
  template <typename T1> static T1 ignoreAndReturn(const T1 b) {
    unit _x = unit::tt;
    return b;
  }

  static int test1();

  template <typename T1, typename T2, MapsTo<T2, T1> F1>
  static T2 transform(const T1 ma, F1 &&f) {
    T1 x = ma;
    return f(x);
  }

  static int test2();

  template <typename T1, typename T2, typename T3, MapsTo<T2, T1> F1,
            MapsTo<T3, T2> F2>
  static T3 nested(const T1 a, F1 &&f, F2 &&g) {
    T1 x = a;
    T2 y = f(x);
    return g(y);
  }

  static int test3();

  static int test4();

  static std::shared_ptr<List::list<int>> intToList(const int n);

  static std::shared_ptr<List::list<int>> test5();

  static int test6();
};
