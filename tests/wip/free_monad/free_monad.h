#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct Unit {
  struct tt;
  using unit = std::variant<tt>;
  struct tt {
    static std::shared_ptr<unit> make();
  };
};

struct FreeMonad {
  struct IO {
    template <typename x> struct pure;
    template <typename x> struct bind;
    template <typename x> struct get_line;
    template <typename x> struct print;
    template <typename x>
    using IO = std::variant<pure<x>, bind<x>, get_line<x>, print<x>>;
    template <typename x> struct pure {
      x _a0;
      static std::shared_ptr<IO<x>> make(x _a0) {
        return std::make_shared<IO<x>>(pure<x>{_a0});
      }
    };
    template <typename x> struct bind {
      std::shared_ptr<IO<unknown>> _a0;
      std::function<std::shared_ptr<IO<x>>(unknown)> _a1;
      static std::shared_ptr<IO<x>>
      make(std::shared_ptr<IO<unknown>> _a0,
           std::function<std::shared_ptr<IO<x>>(unknown)> _a1) {
        return std::make_shared<IO<x>>(bind<x>{_a0, _a1});
      }
    };
    template <typename x> struct get_line {
      static std::shared_ptr<IO<x>> make() {
        return std::make_shared<IO<x>>(get_line<x>{});
      }
    };
    template <typename x> struct print {
      std::string _a0;
      static std::shared_ptr<IO<x>> make(std::string _a0) {
        return std::make_shared<IO<x>>(print<x>{_a0});
      }
    };
  };

  template <
      typename T1, typename T2, MapsTo<T1, unknown> F0,
      MapsTo<T1, std::shared_ptr<typename IO::IO<unknown>>, T1,
             std::function<std::shared_ptr<typename IO::IO<unknown>>(unknown)>,
             std::function<T1(unknown)>>
          F1,
      MapsTo<T1, std::string> F3>
  T1 IO_rect(F0 &&f, F1 &&f0, const T1 f1, F3 &&f2,
             const std::shared_ptr<typename IO::IO<T2>> i) {
    return std::visit(
        Overloaded{
            [&](const typename IO::pure<T2> _args) -> T1 {
              T2 a = _args._a0;
              return f("dummy", a);
            },
            [&](const typename IO::bind<T2> _args) -> T1 {
              std::shared_ptr<typename IO::IO<unknown>> i0 = _args._a0;
              std::function<std::shared_ptr<typename IO::IO<T2>>(unknown)> i1 =
                  _args._a1;
              return f0("dummy", "dummy", i0,
                        IO_rect<T1, T2>(f, f0, f1, f2, i0), i1, [&](unknown a) {
                          return IO_rect<T1, T2>(f, f0, f1, f2, i1(a));
                        });
            },
            [&](const typename IO::get_line<T2> _args) -> T1 { return f1; },
            [&](const typename IO::print<T2> _args) -> T1 {
              std::string s = _args._a0;
              return f2(s);
            }},
        *i);
  }

  template <
      typename T1, typename T2, MapsTo<T1, unknown> F0,
      MapsTo<T1, std::shared_ptr<typename IO::IO<unknown>>, T1,
             std::function<std::shared_ptr<typename IO::IO<unknown>>(unknown)>,
             std::function<T1(unknown)>>
          F1,
      MapsTo<T1, std::string> F3>
  T1 IO_rec(F0 &&f, F1 &&f0, const T1 f1, F3 &&f2,
            const std::shared_ptr<typename IO::IO<T2>> i) {
    return std::visit(
        Overloaded{
            [&](const typename IO::pure<T2> _args) -> T1 {
              T2 a = _args._a0;
              return f("dummy", a);
            },
            [&](const typename IO::bind<T2> _args) -> T1 {
              std::shared_ptr<typename IO::IO<unknown>> i0 = _args._a0;
              std::function<std::shared_ptr<typename IO::IO<T2>>(unknown)> i1 =
                  _args._a1;
              return f0("dummy", "dummy", i0, IO_rec<T1, T2>(f, f0, f1, f2, i0),
                        i1, [&](unknown a) {
                          return IO_rec<T1, T2>(f, f0, f1, f2, i1(a));
                        });
            },
            [&](const typename IO::get_line<T2> _args) -> T1 { return f1; },
            [&](const typename IO::print<T2> _args) -> T1 {
              std::string s = _args._a0;
              return f2(s);
            }},
        *i);
  }

  static inline const std::shared_ptr<
      typename IO::IO<std::shared_ptr<typename Unit::unit>>>
      test = IO::pure<std::shared_ptr<typename Unit::unit>>::make(
          Unit::tt::make());
};
