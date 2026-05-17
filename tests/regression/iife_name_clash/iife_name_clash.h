#ifndef INCLUDED_IIFE_NAME_CLASH
#define INCLUDED_IIFE_NAME_CLASH

#include <type_traits>
#include <utility>
#include <variant>

struct IifeNameClash {
  struct wrapper {
    // TYPES
    struct Wrap {
      unsigned int n;
    };

    struct Empty {};

    using variant_t = std::variant<Wrap, Empty>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    wrapper() {}

    explicit wrapper(Wrap _v) : v_(std::move(_v)) {}

    explicit wrapper(Empty _v) : v_(_v) {}

    wrapper(const wrapper &_other) : v_(std::move(_other.clone().v_)) {}

    wrapper(wrapper &&_other) noexcept : v_(std::move(_other.v_)) {}

    wrapper &operator=(const wrapper &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    wrapper &operator=(wrapper &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    wrapper clone() const {
      if (std::holds_alternative<Wrap>(this->v())) {
        const auto &[n] = std::get<Wrap>(this->v());
        return wrapper(Wrap{n});
      } else {
        return wrapper(Empty{});
      }
    }

    // CREATORS
    static wrapper wrap(unsigned int n) { return wrapper(Wrap{n}); }

    static wrapper empty() { return wrapper(Empty{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, unsigned int &>
  static T1 wrapper_rect(F0 &&f, T1 f0, const wrapper &w) {
    if (std::holds_alternative<typename wrapper::Wrap>(w.v())) {
      const auto &[n0] = std::get<typename wrapper::Wrap>(w.v());
      return f(n0);
    } else {
      return f0;
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, unsigned int &>
  static T1 wrapper_rec(F0 &&f, T1 f0, const wrapper &w) {
    if (std::holds_alternative<typename wrapper::Wrap>(w.v())) {
      const auto &[n0] = std::get<typename wrapper::Wrap>(w.v());
      return f(n0);
    } else {
      return f0;
    }
  }

  static unsigned int double_get(const wrapper &w1, const wrapper &w2);
};

#endif // INCLUDED_IIFE_NAME_CLASH
