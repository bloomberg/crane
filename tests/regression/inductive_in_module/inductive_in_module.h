#ifndef INCLUDED_INDUCTIVE_IN_MODULE
#define INCLUDED_INDUCTIVE_IN_MODULE

#include <any>
#include <type_traits>
#include <utility>
#include <variant>

struct InductiveInModule {
  struct Inner {
    enum class Color { RED, GREEN, BLUE };

    template <typename T1> static T1 color_rect(T1 f, T1 f0, T1 f1, Color c) {
      switch (c) {
      case Color::RED: {
        return f;
      } break;
      case Color::GREEN: {
        return f0;
      } break;
      case Color::BLUE: {
        return f1;
      } break;
      default:
        std::unreachable();
      }
    }

    template <typename T1> static T1 color_rec(T1 f, T1 f0, T1 f1, Color c) {
      switch (c) {
      case Color::RED: {
        return f;
      } break;
      case Color::GREEN: {
        return f0;
      } break;
      case Color::BLUE: {
        return f1;
      } break;
      default:
        std::unreachable();
      }
    }

    static inline const Color default_color = Color::RED;
    static uint64_t color_to_nat(Color c);
  };

  static inline const uint64_t test_color =
      Inner::color_to_nat(Inner::Color::RED);

  struct Outer {
    struct Middle {
      template <typename A> struct option {
        // TYPES
        struct None {};

        struct Some {
          A a;
        };

        using variant_t = std::variant<None, Some>;

      private:
        // DATA
        variant_t v_;

      public:
        // CREATORS
        option() {}

        explicit option(None _v) : v_(_v) {}

        explicit option(Some _v) : v_(std::move(_v)) {}

        template <typename _U> explicit option(const option<_U> &_other) {
          if (std::holds_alternative<typename option<_U>::None>(_other.v())) {
            this->v_ = None{};
          } else {
            const auto &[a] = std::get<typename option<_U>::Some>(_other.v());
            this->v_ = Some{[&]() -> A {
              if constexpr (std::is_same_v<_U, std::any>) {
                if (a.type() == typeid(A))
                  return std::any_cast<A>(a);
                if constexpr (requires {
                                typename A::first_type;
                                typename A::second_type;
                              }) {
                  const auto &[_k, _v] =
                      std::any_cast<std::pair<std::any, std::any>>(a);
                  return A{
                      [&]() -> typename A::first_type {
                        if constexpr (std::is_same_v<typename A::first_type,
                                                     std::any>)
                          return _k;
                        else
                          return std::any_cast<typename A::first_type>(_k);
                      }(),
                      [&]() -> typename A::second_type {
                        if constexpr (std::is_same_v<typename A::second_type,
                                                     std::any>)
                          return _v;
                        else
                          return std::any_cast<typename A::second_type>(_v);
                      }()};
                }
                return std::any_cast<A>(a);
              } else
                return A(a);
            }()};
          }
        }

        static option<A> none() { return option(None{}); }

        static option<A> some(A a) { return option(Some{std::move(a)}); }

        // MANIPULATORS
        inline variant_t &v_mut() { return v_; }

        // ACCESSORS
        const variant_t &v() const { return v_; }
      };

      template <typename T1, typename T2, typename F1>
        requires std::is_invocable_r_v<T2, F1 &, T1 &>
      static T2 option_rect(T2 f, F1 &&f0, const option<T1> &o) {
        if (std::holds_alternative<typename option<T1>::None>(o.v())) {
          return f;
        } else {
          const auto &[a0] = std::get<typename option<T1>::Some>(o.v());
          return f0(a0);
        }
      }

      template <typename T1, typename T2, typename F1>
        requires std::is_invocable_r_v<T2, F1 &, T1 &>
      static T2 option_rec(T2 f, F1 &&f0, const option<T1> &o) {
        if (std::holds_alternative<typename option<T1>::None>(o.v())) {
          return f;
        } else {
          const auto &[a0] = std::get<typename option<T1>::Some>(o.v());
          return f0(a0);
        }
      }

      template <typename T1>
      static T1 get_or_default(T1 default0, const option<T1> &o) {
        if (std::holds_alternative<typename option<T1>::None>(o.v())) {
          return default0;
        } else {
          const auto &[a0] = std::get<typename option<T1>::Some>(o.v());
          return a0;
        }
      }
    };

    static inline const uint64_t test_option =
        Middle::template get_or_default<uint64_t>(
            UINT64_C(42),
            Middle::template option<uint64_t>::some(UINT64_C(99)));
  };

  static inline const uint64_t final_test = Outer::test_option;
};

#endif // INCLUDED_INDUCTIVE_IN_MODULE
