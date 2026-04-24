#ifndef INCLUDED_INDUCTIVE_IN_MODULE
#define INCLUDED_INDUCTIVE_IN_MODULE

#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> struct is_shared_ptr : std::false_type {};

template <typename T>
struct is_shared_ptr<std::shared_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  return x ? std::make_unique<T>(x->clone()) : nullptr;
}

template <typename T>
std::shared_ptr<T> clone_value(const std::shared_ptr<T> &x) {
  return x ? std::make_shared<T>(x->clone()) : nullptr;
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using TargetBare = std::remove_cvref_t<Target>;
  using SourceBare = std::remove_cvref_t<Source>;
  if constexpr (is_unique_ptr<TargetBare>::value) {
    using Inner = typename is_unique_ptr<TargetBare>::element_type;
    if constexpr (is_unique_ptr<SourceBare>::value) {
      using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires {
                             typename Inner::crane_element_type;
                             x->template clone_as<
                                 typename Inner::crane_element_type>();
                           }) {
        return std::make_unique<Inner>(
            x->template clone_as<typename Inner::crane_element_type>());
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_unique<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x.clone());
      }
    }
  } else if constexpr (is_shared_ptr<TargetBare>::value) {
    using Inner = typename is_shared_ptr<TargetBare>::element_type;
    if constexpr (is_shared_ptr<SourceBare>::value) {
      using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else if constexpr (is_unique_ptr<SourceBare>::value) {
      if (!x)
        return nullptr;
      if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_shared<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x.clone());
      }
    }
  } else if constexpr (std::is_same_v<TargetBare, SourceBare>) {
    return clone_value(x);
  } else if constexpr (is_unique_ptr<SourceBare>::value) {
    using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (is_shared_ptr<SourceBare>::value) {
    using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (requires {
                         typename TargetBare::crane_element_type;
                         x.template clone_as<
                             typename TargetBare::crane_element_type>();
                       }) {
    return x.template clone_as<typename TargetBare::crane_element_type>();
  } else if constexpr (requires { x.template clone_as<TargetBare>(); }) {
    return x.template clone_as<TargetBare>();
  } else {
    return Target(x);
  }
}

struct InductiveInModule {
  struct Inner {
    enum class Color { e_RED, e_GREEN, e_BLUE };

    template <typename T1>
    static T1 color_rect(const T1 f, const T1 f0, const T1 f1, const Color c) {
      switch (c) {
      case Color::e_RED: {
        return f;
      }
      case Color::e_GREEN: {
        return f0;
      }
      case Color::e_BLUE: {
        return f1;
      }
      default:
        std::unreachable();
      }
    }

    template <typename T1>
    static T1 color_rec(const T1 f, const T1 f0, const T1 f1, const Color c) {
      switch (c) {
      case Color::e_RED: {
        return f;
      }
      case Color::e_GREEN: {
        return f0;
      }
      case Color::e_BLUE: {
        return f1;
      }
      default:
        std::unreachable();
      }
    }

    static inline const Color default_color = Color::e_RED;
    __attribute__((pure)) static unsigned int color_to_nat(const Color c);
  };

  static inline const unsigned int test_color =
      Inner::color_to_nat(Inner::Color::e_RED);

  struct Outer {
    struct Middle {
      template <typename t_A> struct option {
        // TYPES
        struct None {};

        struct Some {
          t_A d_a0;
        };

        using variant_t = std::variant<None, Some>;

      private:
        // DATA
        variant_t d_v_;

      public:
        // CREATORS
        option() {}

        explicit option(None _v) : d_v_(_v) {}

        explicit option(Some _v) : d_v_(std::move(_v)) {}

        option(const option<t_A> &_other)
            : d_v_(std::move(_other.clone().d_v_)) {}

        option(option<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

        __attribute__((pure)) option<t_A> &
        operator=(const option<t_A> &_other) {
          d_v_ = std::move(_other.clone().d_v_);
          return *this;
        }

        __attribute__((pure)) option<t_A> &operator=(option<t_A> &&_other) {
          d_v_ = std::move(_other.d_v_);
          return *this;
        }

        // ACCESSORS
        __attribute__((pure)) option<t_A> clone() const {
          auto &&_sv = *(this);
          if (std::holds_alternative<None>(_sv.v())) {
            return option<t_A>(None{});
          } else {
            const auto &[d_a0] = std::get<Some>(_sv.v());
            return option<t_A>(Some{clone_as_value<t_A>(d_a0)});
          }
        }

        template <typename _CloneT0>
        __attribute__((pure)) option<_CloneT0> clone_as() const {
          auto &&_sv = *(this);
          if (std::holds_alternative<None>(_sv.v())) {
            return option<_CloneT0>(typename option<_CloneT0>::None{});
          } else {
            const auto &[d_a0] = std::get<Some>(_sv.v());
            return option<_CloneT0>(typename option<_CloneT0>::Some{
                clone_as_value<_CloneT0>(d_a0)});
          }
        }

        // CREATORS
        constexpr static option<t_A> none() { return option(None{}); }

        __attribute__((pure)) static option<t_A> some(t_A a0) {
          return option(Some{std::move(a0)});
        }

        // MANIPULATORS
        __attribute__((pure)) variant_t &v_mut() { return d_v_; }

        // ACCESSORS
        __attribute__((pure)) option<t_A> *operator->() { return this; }

        __attribute__((pure)) const option<t_A> *operator->() const {
          return this;
        }

        __attribute__((pure)) bool operator!=(std::nullptr_t) const {
          return true;
        }

        __attribute__((pure)) bool operator==(std::nullptr_t) const {
          return false;
        }

        // MANIPULATORS
        void reset() { *this = option<t_A>(); }

        // ACCESSORS
        __attribute__((pure)) const variant_t &v() const { return d_v_; }
      };

      template <typename T1, typename T2, MapsTo<T2, T1> F1>
      static T2 option_rect(const T2 f, F1 &&f0, const option<T1> &o) {
        if (std::holds_alternative<typename option<T1>::None>(o.v())) {
          return f;
        } else {
          const auto &[d_a0] = std::get<typename option<T1>::Some>(o.v());
          return f0(d_a0);
        }
      }

      template <typename T1, typename T2, MapsTo<T2, T1> F1>
      static T2 option_rec(const T2 f, F1 &&f0, const option<T1> &o) {
        if (std::holds_alternative<typename option<T1>::None>(o.v())) {
          return f;
        } else {
          const auto &[d_a0] = std::get<typename option<T1>::Some>(o.v());
          return f0(d_a0);
        }
      }

      template <typename T1>
      static T1 get_or_default(const T1 default0, const option<T1> &o) {
        if (std::holds_alternative<typename option<T1>::None>(o.v())) {
          return default0;
        } else {
          const auto &[d_a0] = std::get<typename option<T1>::Some>(o.v());
          return d_a0;
        }
      }
    };

    static inline const unsigned int test_option =
        Middle::template get_or_default<unsigned int>(
            42u, Middle::template option<unsigned int>::some(99u));
  };

  static inline const unsigned int final_test = Outer::test_option;
};

#endif // INCLUDED_INDUCTIVE_IN_MODULE
