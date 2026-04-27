#ifndef INCLUDED_RECORD_PROJ
#define INCLUDED_RECORD_PROJ

#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct RecordProj {
  struct Point {
    unsigned int x;
    unsigned int y;

    __attribute__((pure)) Point *operator->() { return this; }

    __attribute__((pure)) const Point *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) Point clone() const {
      return Point{
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).x),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).y)};
    }
  };

  struct ComplexRecord {
    unsigned int field1;
    unsigned int field2;
    unsigned int field3;

    __attribute__((pure)) ComplexRecord *operator->() { return this; }

    __attribute__((pure)) const ComplexRecord *operator->() const {
      return this;
    }

    // ACCESSORS
    __attribute__((pure)) ComplexRecord clone() const {
      return ComplexRecord{
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).field1),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).field2),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).field3)};
    }
  };

  __attribute__((pure)) static unsigned int weird_access(const Point &p);
  __attribute__((pure)) static unsigned int
  complex_access(const ComplexRecord &c);
  __attribute__((pure)) static unsigned int
  nested_record_match(const Point &p1, const Point &p2);

  template <MapsTo<unsigned int, unsigned int> F0>
  __attribute__((pure)) static unsigned int apply_to_field(F0 &&f,
                                                           const Point &p) {
    unsigned int a = p.x;
    unsigned int b = p.y;
    return (f(a) + f(b));
  }

  static inline const unsigned int test1 = weird_access(Point{10u, 20u});
  static inline const unsigned int test2 =
      complex_access(ComplexRecord{5u, 10u, 15u});
};

#endif // INCLUDED_RECORD_PROJ
