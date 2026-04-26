#ifndef INCLUDED_RECORD_DEFAULTS
#define INCLUDED_RECORD_DEFAULTS

#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_unique<T>(x->clone()) : nullptr;
  } else {
    return x ? std::make_unique<T>(*x) : nullptr;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using T = std::remove_cvref_t<Target>;
  using S = std::remove_cvref_t<Source>;
  if constexpr (requires(const S &s) {
                  s.has_value();
                  *s;
                }) {
    if (!x.has_value())
      return T{};
    using TInner = std::remove_cvref_t<decltype(*std::declval<const T &>())>;
    return T{clone_as_value<TInner>(*x)};
  } else if constexpr (std::is_same_v<T, S>) {
    if constexpr (is_unique_ptr<T>::value) {
      return clone_value(x);
    } else if constexpr (requires { x.clone(); }) {
      return x.clone();
    } else {
      return x;
    }
  } else if constexpr (is_unique_ptr<S>::value) {
    if (!x)
      return T{};
    return clone_as_value<T>(*x);
  } else if constexpr (is_unique_ptr<T>::value) {
    using Inner = typename is_unique_ptr<T>::element_type;
    return std::make_unique<Inner>(clone_as_value<Inner>(x));
  } else {
    return T(x);
  }
}

struct RecordDefaults {
  struct Config {
    unsigned int cfg_width;
    unsigned int cfg_height;
    unsigned int cfg_depth;
    bool cfg_debug;

    __attribute__((pure)) Config *operator->() { return this; }

    __attribute__((pure)) const Config *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) Config clone() const {
      return Config{(*(this)).cfg_width, (*(this)).cfg_height,
                    (*(this)).cfg_depth, (*(this)).cfg_debug};
    }
  };

  static inline const Config default_config = Config{80u, 24u, 1u, false};
  __attribute__((pure)) static Config set_width(unsigned int w,
                                                const Config &c);
  __attribute__((pure)) static Config set_debug(bool d, const Config &c);

  struct Point {
    unsigned int px;
    unsigned int py;

    __attribute__((pure)) Point *operator->() { return this; }

    __attribute__((pure)) const Point *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) Point clone() const {
      return Point{(*(this)).px, (*(this)).py};
    }
  };

  struct Rect {
    Point origin;
    Point extent;

    __attribute__((pure)) Rect *operator->() { return this; }

    __attribute__((pure)) const Rect *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) Rect clone() const {
      return Rect{(*(this)).origin, (*(this)).extent};
    }
  };

  __attribute__((pure)) static unsigned int rect_area(const Rect &r);
  __attribute__((pure)) static Rect make_rect(unsigned int x, unsigned int y,
                                              unsigned int w, unsigned int h);
  __attribute__((pure)) static unsigned int total_cells(const Config &c);
  static inline const unsigned int test_default_width =
      default_config.cfg_width;
  static inline const bool test_default_debug = default_config.cfg_debug;
  static inline const unsigned int test_cells = total_cells(default_config);
  static inline const unsigned int test_modified =
      total_cells(set_width(120u, set_debug(true, default_config)));
  static inline const unsigned int test_rect_area =
      rect_area(make_rect(0u, 0u, 10u, 5u));
};

#endif // INCLUDED_RECORD_DEFAULTS
