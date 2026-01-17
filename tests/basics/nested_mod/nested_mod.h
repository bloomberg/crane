#include <algorithm>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

std::pair<unsigned int, unsigned int> divmod(const unsigned int x,
                                             const unsigned int y,
                                             const unsigned int q,
                                             const unsigned int u);

unsigned int div(const unsigned int x, const unsigned int y);

struct Outer {
  struct color {
  public:
    struct Red {};
    struct Green {};
    struct Blue {};
    using variant_t = std::variant<Red, Green, Blue>;

  private:
    variant_t v_;
    explicit color(Red x) : v_(std::move(x)) {}
    explicit color(Green x) : v_(std::move(x)) {}
    explicit color(Blue x) : v_(std::move(x)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<color> Red_() {
        return std::shared_ptr<color>(new color(Red{}));
      }
      static std::shared_ptr<color> Green_() {
        return std::shared_ptr<color>(new color(Green{}));
      }
      static std::shared_ptr<color> Blue_() {
        return std::shared_ptr<color>(new color(Blue{}));
      }
    };
    const variant_t &v() const { return v_; }
  };

  struct Inner {
    struct shape {
    public:
      struct Circle {
        unsigned int _a0;
      };
      struct Square {
        unsigned int _a0;
      };
      struct Triangle {
        unsigned int _a0;
        unsigned int _a1;
        unsigned int _a2;
      };
      using variant_t = std::variant<Circle, Square, Triangle>;

    private:
      variant_t v_;
      explicit shape(Circle x) : v_(std::move(x)) {}
      explicit shape(Square x) : v_(std::move(x)) {}
      explicit shape(Triangle x) : v_(std::move(x)) {}

    public:
      struct ctor {
        ctor() = delete;
        static std::shared_ptr<shape> Circle_(unsigned int a0) {
          return std::shared_ptr<shape>(new shape(Circle{a0}));
        }
        static std::shared_ptr<shape> Square_(unsigned int a0) {
          return std::shared_ptr<shape>(new shape(Square{a0}));
        }
        static std::shared_ptr<shape>
        Triangle_(unsigned int a0, unsigned int a1, unsigned int a2) {
          return std::shared_ptr<shape>(new shape(Triangle{a0, a1, a2}));
        }
      };
      const variant_t &v() const { return v_; }
    };

    static unsigned int area(const std::shared_ptr<shape> &s);
  };

  static unsigned int shape_with_color(const std::shared_ptr<Inner::shape> &s,
                                       const std::shared_ptr<color> &c);

  static unsigned int color_code(const std::shared_ptr<color> &c);
};

const std::shared_ptr<Outer::Inner::shape> my_circle =
    Outer::Inner::shape::ctor::Circle_((((((0 + 1) + 1) + 1) + 1) + 1));

const std::shared_ptr<Outer::color> my_color = Outer::color::ctor::Red_();

const unsigned int test_area = Outer::Inner::area(my_circle);

const unsigned int test_combined = Outer::shape_with_color(my_circle, my_color);

const unsigned int test_color = Outer::color_code(my_color);
