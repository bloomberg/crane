#ifndef INCLUDED_INDUCTIVE_IN_MODULE
#define INCLUDED_INDUCTIVE_IN_MODULE

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

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
    static unsigned int color_to_nat(const Color c);
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

        option<t_A> &operator=(const option<t_A> &_other) {
          d_v_ = std::move(_other.clone().d_v_);
          return *this;
        }

        option<t_A> &operator=(option<t_A> &&_other) {
          d_v_ = std::move(_other.d_v_);
          return *this;
        }

        // ACCESSORS
        option<t_A> clone() const {
          auto &&_sv = *(this);
          if (std::holds_alternative<None>(_sv.v())) {
            return option<t_A>(None{});
          } else {
            const auto &[d_a0] = std::get<Some>(_sv.v());
            return option<t_A>(Some{d_a0});
          }
        }

        // CREATORS
        template <typename _U> explicit option(const option<_U> &_other) {
          if (std::holds_alternative<typename option<_U>::None>(_other.v())) {
            d_v_ = None{};
          } else {
            const auto &[d_a0] =
                std::get<typename option<_U>::Some>(_other.v());
            d_v_ = Some{t_A(d_a0)};
          }
        }

        static option<t_A> none() { return option(None{}); }

        static option<t_A> some(t_A a0) { return option(Some{std::move(a0)}); }

        // MANIPULATORS
        inline variant_t &v_mut() { return d_v_; }

        // ACCESSORS
        const variant_t &v() const { return d_v_; }
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
