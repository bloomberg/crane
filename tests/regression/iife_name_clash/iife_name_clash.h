#ifndef INCLUDED_IIFE_NAME_CLASH
#define INCLUDED_IIFE_NAME_CLASH

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct IifeNameClash {
  struct wrapper {
    // TYPES
    struct Wrap {
      unsigned int d_n;
    };

    struct Empty {};

    using variant_t = std::variant<Wrap, Empty>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit wrapper(Wrap _v) : d_v_(std::move(_v)) {}

    explicit wrapper(Empty _v) : d_v_(_v) {}

    static std::shared_ptr<wrapper> wrap(unsigned int n) {
      return std::make_shared<wrapper>(Wrap{std::move(n)});
    }

    static std::shared_ptr<wrapper> empty() {
      return std::make_shared<wrapper>(Empty{});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0>
  static T1 wrapper_rect(F0 &&f, const T1 f0,
                         const std::shared_ptr<wrapper> &w) {
    if (std::holds_alternative<typename wrapper::Wrap>(w->v())) {
      const auto &[d_n] = std::get<typename wrapper::Wrap>(w->v());
      return f(d_n);
    } else {
      return f0;
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F0>
  static T1 wrapper_rec(F0 &&f, const T1 f0,
                        const std::shared_ptr<wrapper> &w) {
    if (std::holds_alternative<typename wrapper::Wrap>(w->v())) {
      const auto &[d_n] = std::get<typename wrapper::Wrap>(w->v());
      return f(d_n);
    } else {
      return f0;
    }
  }

  __attribute__((pure)) static unsigned int
  double_get(const std::shared_ptr<wrapper> &w1,
             const std::shared_ptr<wrapper> &w2);
};

#endif // INCLUDED_IIFE_NAME_CLASH
