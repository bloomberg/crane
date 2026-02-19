#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct SingletonRecord {
  struct wrapper {
  public:
    struct Build_wrapper {
      unsigned int _a0;
    };
    using variant_t = std::variant<Build_wrapper>;

  private:
    variant_t v_;
    explicit wrapper(Build_wrapper _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<wrapper> Build_wrapper_(unsigned int a0) {
        return std::shared_ptr<wrapper>(new wrapper(Build_wrapper{a0}));
      }
    };
    const variant_t &v() const { return v_; }
  };

  static unsigned int value(const std::shared_ptr<wrapper> &w);

  static inline const std::shared_ptr<wrapper> wrapped_five = 5u;

  static unsigned int get_value(const std::shared_ptr<wrapper> &w);

  static unsigned int get_value2(const std::shared_ptr<wrapper> &w);

  static unsigned int unwrap(const std::shared_ptr<wrapper> &w);

  static std::shared_ptr<wrapper>
  double_wrapped(const std::shared_ptr<wrapper> &w);

  template <typename A> struct box {
  public:
    struct Build_box {
      A _a0;
    };
    using variant_t = std::variant<Build_box>;

  private:
    variant_t v_;
    explicit box(Build_box _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<box<A>> Build_box_(A a0) {
        return std::shared_ptr<box<A>>(new box<A>(Build_box{a0}));
      }
    };
    const variant_t &v() const { return v_; }
  };

  template <typename T1> static T1 contents(const std::shared_ptr<box<T1>> &b) {
    return b;
  }

  static inline const std::shared_ptr<box<unsigned int>> boxed_three = 3u;

  template <typename T1> static T1 unbox(const std::shared_ptr<box<T1>> &b) {
    return b;
  }

  static inline const std::shared_ptr<box<std::shared_ptr<box<unsigned int>>>>
      nested_box = boxed_three;

  static inline const unsigned int double_unbox = nested_box;

  struct fn_wrapper {
  public:
    struct Build_fn_wrapper {
      std::function<unsigned int(unsigned int)> _a0;
    };
    using variant_t = std::variant<Build_fn_wrapper>;

  private:
    variant_t v_;
    explicit fn_wrapper(Build_fn_wrapper _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<fn_wrapper>
      Build_fn_wrapper_(std::function<unsigned int(unsigned int)> a0) {
        return std::shared_ptr<fn_wrapper>(
            new fn_wrapper(Build_fn_wrapper{a0}));
      }
    };
    const variant_t &v() const { return v_; }
  };

  static unsigned int fn(const std::shared_ptr<fn_wrapper> &,
                         const unsigned int);

  static inline const std::shared_ptr<fn_wrapper> my_fn_wrapper =
      [](const unsigned int _x0) { return (1u + _x0); };

  static unsigned int apply_wrapped(const std::shared_ptr<fn_wrapper> &,
                                    const unsigned int);

  static inline const unsigned int test_get = get_value(wrapped_five);

  static inline const unsigned int test_get2 = get_value2(wrapped_five);

  static inline const unsigned int test_unwrap = unwrap(wrapped_five);

  static inline const unsigned int test_double = double_wrapped(wrapped_five);

  static inline const unsigned int test_unbox =
      unbox<unsigned int>(boxed_three);

  static inline const unsigned int test_double_unbox = double_unbox;

  static inline const unsigned int test_fn = apply_wrapped(my_fn_wrapper, 7u);
};
