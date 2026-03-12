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
    enum class color { Red, Green, Blue };

    template <typename T1>
    static T1 color_rect(const T1 f, const T1 f0, const T1 f1, const color c) {
      return [&](void) {
        switch (c) {
        case color::Red: {
          return f;
        }
        case color::Green: {
          return f0;
        }
        case color::Blue: {
          return f1;
        }
        }
      }();
    }

    template <typename T1>
    static T1 color_rec(const T1 f, const T1 f0, const T1 f1, const color c) {
      return [&](void) {
        switch (c) {
        case color::Red: {
          return f;
        }
        case color::Green: {
          return f0;
        }
        case color::Blue: {
          return f1;
        }
        }
      }();
    }

    static inline const color default_color = color::Red;
    static unsigned int color_to_nat(const color c);
  };

  static inline const unsigned int test_color =
      Inner::color_to_nat(Inner::color::Red);

  struct Outer {
    struct Middle {
      template <typename A> struct option {
        // TYPES
        struct None {};

        struct Some {
          A _a0;
        };

        using variant_t = std::variant<None, Some>;

      private:
        // DATA
        variant_t v_;

        // CREATORS
        explicit option(None _v) : v_(std::move(_v)) {}

        explicit option(Some _v) : v_(std::move(_v)) {}

      public:
        // TYPES
        struct ctor {
          ctor() = delete;

          static std::shared_ptr<option<A>> None_() {
            return std::shared_ptr<option<A>>(new option<A>(None{}));
          }

          static std::shared_ptr<option<A>> Some_(A a0) {
            return std::shared_ptr<option<A>>(new option<A>(Some{a0}));
          }

          static std::unique_ptr<option<A>> None_uptr() {
            return std::unique_ptr<option<A>>(new option<A>(None{}));
          }

          static std::unique_ptr<option<A>> Some_uptr(A a0) {
            return std::unique_ptr<option<A>>(new option<A>(Some{a0}));
          }
        };

        // MANIPULATORS
        variant_t &v_mut() { return v_; }

        // ACCESSORS
        const variant_t &v() const { return v_; }
      };

      template <typename T1, typename T2, MapsTo<T2, T1> F1>
      static T2 option_rect(const T2 f, F1 &&f0,
                            const std::shared_ptr<option<T1>> &o) {
        return std::visit(
            Overloaded{
                [&](const typename option<T1>::None _args) -> T2 { return f; },
                [&](const typename option<T1>::Some _args) -> T2 {
                  T1 a = _args._a0;
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
                  T1 a = _args._a0;
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
                         T1 x = _args._a0;
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
