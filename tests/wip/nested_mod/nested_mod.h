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

std::pair<unsigned int, unsigned int> divmod(const unsigned int x,
                                             const unsigned int y,
                                             const unsigned int q,
                                             const unsigned int u);

unsigned int div(const unsigned int x, const unsigned int y);

struct Outer {
  enum class color { Red, Green, Blue };

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
      explicit shape(Circle _v) : v_(std::move(_v)) {}
      explicit shape(Square _v) : v_(std::move(_v)) {}
      explicit shape(Triangle _v) : v_(std::move(_v)) {}

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
        static std::unique_ptr<shape> Circle_uptr(unsigned int a0) {
          return std::unique_ptr<shape>(new shape(Circle{a0}));
        }
        static std::unique_ptr<shape> Square_uptr(unsigned int a0) {
          return std::unique_ptr<shape>(new shape(Square{a0}));
        }
        static std::unique_ptr<shape>
        Triangle_uptr(unsigned int a0, unsigned int a1, unsigned int a2) {
          return std::unique_ptr<shape>(new shape(Triangle{a0, a1, a2}));
        }
      };
      const variant_t &v() const { return v_; }
      variant_t &v_mut() { return v_; }
    };

    static unsigned int area(const std::shared_ptr<shape> &s);
  };

  static unsigned int shape_with_color(const std::shared_ptr<Inner::shape> &s,
                                       const color c);

  static unsigned int color_code(const color c);
};

const std::shared_ptr<Outer::Inner::shape> my_circle =
    Outer::Inner::shape::ctor::Circle_((((((0 + 1) + 1) + 1) + 1) + 1));

const outer::color my_color = color::Red;

const unsigned int test_area = Outer::Inner::area(my_circle);

const unsigned int test_combined = Outer::shape_with_color(my_circle, my_color);

const unsigned int test_color = Outer::color_code(my_color);
