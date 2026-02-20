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

struct EmptyMatch {
  struct empty {
    empty() = delete;
  };

  template <typename T1>
  static T1 empty_rect(const std::shared_ptr<empty> &_x) {
    throw std::logic_error("absurd case");
  }

  template <typename T1> static T1 empty_rec(const std::shared_ptr<empty> &_x) {
    throw std::logic_error("absurd case");
  }

  template <typename T1> static T1 absurd(const std::shared_ptr<empty> &_x) {
    throw std::logic_error("absurd case");
  }

  static unsigned int from_empty(const std::shared_ptr<empty> &);

  template <typename A, typename B> struct either {
  public:
    struct Left {
      A _a0;
    };
    struct Right {
      B _a0;
    };
    using variant_t = std::variant<Left, Right>;

  private:
    variant_t v_;
    explicit either(Left _v) : v_(std::move(_v)) {}
    explicit either(Right _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<either<A, B>> Left_(A a0) {
        return std::shared_ptr<either<A, B>>(new either<A, B>(Left{a0}));
      }
      static std::shared_ptr<either<A, B>> Right_(B a0) {
        return std::shared_ptr<either<A, B>>(new either<A, B>(Right{a0}));
      }
      static std::unique_ptr<either<A, B>> Left_uptr(A a0) {
        return std::unique_ptr<either<A, B>>(new either<A, B>(Left{a0}));
      }
      static std::unique_ptr<either<A, B>> Right_uptr(B a0) {
        return std::unique_ptr<either<A, B>>(new either<A, B>(Right{a0}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1> F0,
            MapsTo<T3, T2> F1>
  static T3 either_rect(F0 &&f, F1 &&f0,
                        const std::shared_ptr<either<T1, T2>> &e) {
    return std::visit(
        Overloaded{[&](const typename either<T1, T2>::Left _args) -> T3 {
                     T1 a = _args._a0;
                     return f(a);
                   },
                   [&](const typename either<T1, T2>::Right _args) -> T3 {
                     T2 b = _args._a0;
                     return f0(b);
                   }},
        e->v());
  }

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1> F0,
            MapsTo<T3, T2> F1>
  static T3 either_rec(F0 &&f, F1 &&f0,
                       const std::shared_ptr<either<T1, T2>> &e) {
    return std::visit(
        Overloaded{[&](const typename either<T1, T2>::Left _args) -> T3 {
                     T1 a = _args._a0;
                     return f(a);
                   },
                   [&](const typename either<T1, T2>::Right _args) -> T3 {
                     T2 b = _args._a0;
                     return f0(b);
                   }},
        e->v());
  }

  template <typename T1>
  static T1
  handle_left(const std::shared_ptr<either<T1, std::shared_ptr<empty>>> &e) {
    return std::visit(
        Overloaded{
            [](const typename either<T1, std::shared_ptr<empty>>::Left _args)
                -> T1 {
              T1 a = _args._a0;
              return a;
            },
            [](const typename either<T1, std::shared_ptr<empty>>::Right _args)
                -> T1 {
              std::shared_ptr<empty> v = _args._a0;
              return absurd<T1>(std::move(v));
            }},
        e->v());
  }

  static inline const std::shared_ptr<
      either<unsigned int, std::shared_ptr<empty>>>
      test_either =
          either<unsigned int, std::shared_ptr<empty>>::ctor::Left_(5u);

  static inline const unsigned int test_handle =
      handle_left<unsigned int>(test_either);

  template <typename T1, typename T2>
  static std::shared_ptr<either<T1, T2>>
  complex_absurd(const std::shared_ptr<empty> &_x) {
    throw std::logic_error("absurd case");
  }
};
