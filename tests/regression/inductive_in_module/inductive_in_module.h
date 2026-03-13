#ifndef INCLUDED_INDUCTIVE_IN_MODULE
#define INCLUDED_INDUCTIVE_IN_MODULE

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct InductiveInModule {
  struct Inner {
    enum class Color { e_RED, e_GREEN, e_BLUE };

    template <typename T1>
    static T1 color_rect(const T1 f, const T1 f0, const T1 f1, const Color c) {
      return [&](void) {
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
        }
      }();
    }

    template <typename T1>
    static T1 color_rec(const T1 f, const T1 f0, const T1 f1, const Color c) {
      return [&](void) {
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
        }
      }();
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

        // CREATORS
        explicit option(None _v) : d_v_(std::move(_v)) {}

        explicit option(Some _v) : d_v_(std::move(_v)) {}

      public:
        // TYPES
        struct ctor {
          ctor() = delete;

          static std::shared_ptr<option<t_A>> None_() {
            return std::shared_ptr<option<t_A>>(new option<t_A>(None{}));
          }

          static std::shared_ptr<option<t_A>> Some_(t_A a0) {
            return std::shared_ptr<option<t_A>>(new option<t_A>(Some{a0}));
          }

          static std::unique_ptr<option<t_A>> None_uptr() {
            return std::unique_ptr<option<t_A>>(new option<t_A>(None{}));
          }

          static std::unique_ptr<option<t_A>> Some_uptr(t_A a0) {
            return std::unique_ptr<option<t_A>>(new option<t_A>(Some{a0}));
          }
        };

        // MANIPULATORS
        __attribute__((pure)) variant_t &v_mut() { return d_v_; }

        // ACCESSORS
        __attribute__((pure)) const variant_t &v() const { return d_v_; }
      };

      template <typename T1, typename T2, MapsTo<T2, T1> F1>
      static T2 option_rect(const T2 f, F1 &&f0,
                            const std::shared_ptr<option<T1>> &o) {
        return std::visit(
            Overloaded{
                [&](const typename option<T1>::None _args) -> T2 { return f; },
                [&](const typename option<T1>::Some _args) -> T2 {
                  T1 a = _args.d_a0;
                  return f0(a);
                }},
            o->v());
      }

      template <typename T1, typename T2, MapsTo<T2, T1> F1>
      static T2 option_rec(const T2 f, F1 &&f0,
                           const std::shared_ptr<option<T1>> &o) {
        return std::visit(
            Overloaded{
                [&](const typename option<T1>::None _args) -> T2 { return f; },
                [&](const typename option<T1>::Some _args) -> T2 {
                  T1 a = _args.d_a0;
                  return f0(a);
                }},
            o->v());
      }

      template <typename T1>
      static T1 get_or_default(const T1 default0,
                               const std::shared_ptr<option<T1>> &o) {
        return std::visit(
            Overloaded{[&](const typename option<T1>::None _args) -> T1 {
                         return default0;
                       },
                       [](const typename option<T1>::Some _args) -> T1 {
                         T1 x = _args.d_a0;
                         return x;
                       }},
            o->v());
      }
    };

    static inline const unsigned int test_option =
        Middle::template get_or_default<unsigned int>(
            42u, Middle::template option<unsigned int>::ctor::Some_(99u));
  };

  static inline const unsigned int final_test = Outer::test_option;
};

#endif // INCLUDED_INDUCTIVE_IN_MODULE
