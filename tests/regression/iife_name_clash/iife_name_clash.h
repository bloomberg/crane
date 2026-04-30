#ifndef INCLUDED_IIFE_NAME_CLASH
#define INCLUDED_IIFE_NAME_CLASH

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

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
    wrapper() {}

    explicit wrapper(Wrap _v) : d_v_(std::move(_v)) {}

    explicit wrapper(Empty _v) : d_v_(_v) {}

    wrapper(const wrapper &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    wrapper(wrapper &&_other) : d_v_(std::move(_other.d_v_)) {}

    wrapper &operator=(const wrapper &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    wrapper &operator=(wrapper &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    wrapper clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Wrap>(_sv.v())) {
        const auto &[d_n] = std::get<Wrap>(_sv.v());
        return wrapper(Wrap{d_n});
      } else {
        return wrapper(Empty{});
      }
    }

    // CREATORS
    static wrapper wrap(unsigned int n) { return wrapper(Wrap{std::move(n)}); }

    static wrapper empty() { return wrapper(Empty{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0>
  static T1 wrapper_rect(F0 &&f, const T1 f0, const wrapper &w) {
    if (std::holds_alternative<typename wrapper::Wrap>(w.v())) {
      const auto &[d_n] = std::get<typename wrapper::Wrap>(w.v());
      return f(d_n);
    } else {
      return f0;
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F0>
  static T1 wrapper_rec(F0 &&f, const T1 f0, const wrapper &w) {
    if (std::holds_alternative<typename wrapper::Wrap>(w.v())) {
      const auto &[d_n] = std::get<typename wrapper::Wrap>(w.v());
      return f(d_n);
    } else {
      return f0;
    }
  }

  static unsigned int double_get(const wrapper &w1, const wrapper &w2);
};

#endif // INCLUDED_IIFE_NAME_CLASH
