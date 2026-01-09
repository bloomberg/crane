#include <algorithm>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct List {
  template <typename A> struct nil;
  template <typename A> struct cons;
  template <typename A> using list = std::variant<nil<A>, cons<A>>;
  template <typename A> struct nil {
    static std::shared_ptr<list<A>> make() {
      return std::make_shared<list<A>>(nil<A>{});
    }
  };
  template <typename A> struct cons {
    A _a0;
    std::shared_ptr<list<A>> _a1;
    static std::shared_ptr<list<A>> make(A _a0, std::shared_ptr<list<A>> _a1) {
      return std::make_shared<list<A>>(cons<A>{_a0, _a1});
    }
  };
};

struct Matcher {
  static bool char_eq(const int x, const int y);

  struct Regexp {
    struct Any;
    struct Char;
    struct Eps;
    struct Cat;
    struct Alt;
    struct Zero;
    struct Star;
    using regexp = std::variant<Any, Char, Eps, Cat, Alt, Zero, Star>;
    struct Any {
      static std::shared_ptr<regexp> make();
    };
    struct Char {
      int _a0;
      static std::shared_ptr<regexp> make(int _a0);
    };
    struct Eps {
      static std::shared_ptr<regexp> make();
    };
    struct Cat {
      std::shared_ptr<regexp> _a0;
      std::shared_ptr<regexp> _a1;
      static std::shared_ptr<regexp> make(std::shared_ptr<regexp> _a0,
                                          std::shared_ptr<regexp> _a1);
    };
    struct Alt {
      std::shared_ptr<regexp> _a0;
      std::shared_ptr<regexp> _a1;
      static std::shared_ptr<regexp> make(std::shared_ptr<regexp> _a0,
                                          std::shared_ptr<regexp> _a1);
    };
    struct Zero {
      static std::shared_ptr<regexp> make();
    };
    struct Star {
      std::shared_ptr<regexp> _a0;
      static std::shared_ptr<regexp> make(std::shared_ptr<regexp> _a0);
    };
  };

  template <typename T1, MapsTo<T1, int> F1,
            MapsTo<T1, std::shared_ptr<typename Regexp::regexp>, T1,
                   std::shared_ptr<typename Regexp::regexp>, T1>
                F3,
            MapsTo<T1, std::shared_ptr<typename Regexp::regexp>, T1,
                   std::shared_ptr<typename Regexp::regexp>, T1>
                F4,
            MapsTo<T1, std::shared_ptr<typename Regexp::regexp>, T1> F6>
  T1 regexp_rect(const T1 f, F1 &&f0, const T1 f1, F3 &&f2, F4 &&f3,
                 const T1 f4, F6 &&f5,
                 const std::shared_ptr<typename Regexp::regexp> r) {
    return std::visit(
        Overloaded{
            [&](const typename Regexp::Any _args) -> T1 { return f; },
            [&](const typename Regexp::Char _args) -> T1 {
              int c = _args._a0;
              return f0(c);
            },
            [&](const typename Regexp::Eps _args) -> T1 { return f1; },
            [&](const typename Regexp::Cat _args) -> T1 {
              std::shared_ptr<typename Regexp::regexp> r2 = _args._a0;
              std::shared_ptr<typename Regexp::regexp> r3 = _args._a1;
              return f2(r2, regexp_rect<T1>(f, f0, f1, f2, f3, f4, f5, r2), r3,
                        regexp_rect<T1>(f, f0, f1, f2, f3, f4, f5, r3));
            },
            [&](const typename Regexp::Alt _args) -> T1 {
              std::shared_ptr<typename Regexp::regexp> r2 = _args._a0;
              std::shared_ptr<typename Regexp::regexp> r3 = _args._a1;
              return f3(r2, regexp_rect<T1>(f, f0, f1, f2, f3, f4, f5, r2), r3,
                        regexp_rect<T1>(f, f0, f1, f2, f3, f4, f5, r3));
            },
            [&](const typename Regexp::Zero _args) -> T1 { return f4; },
            [&](const typename Regexp::Star _args) -> T1 {
              std::shared_ptr<typename Regexp::regexp> r0 = _args._a0;
              return f5(r0, regexp_rect<T1>(f, f0, f1, f2, f3, f4, f5, r0));
            }},
        *r);
  }

  template <typename T1, MapsTo<T1, int> F1,
            MapsTo<T1, std::shared_ptr<typename Regexp::regexp>, T1,
                   std::shared_ptr<typename Regexp::regexp>, T1>
                F3,
            MapsTo<T1, std::shared_ptr<typename Regexp::regexp>, T1,
                   std::shared_ptr<typename Regexp::regexp>, T1>
                F4,
            MapsTo<T1, std::shared_ptr<typename Regexp::regexp>, T1> F6>
  T1 regexp_rec(const T1 f, F1 &&f0, const T1 f1, F3 &&f2, F4 &&f3, const T1 f4,
                F6 &&f5, const std::shared_ptr<typename Regexp::regexp> r) {
    return std::visit(
        Overloaded{
            [&](const typename Regexp::Any _args) -> T1 { return f; },
            [&](const typename Regexp::Char _args) -> T1 {
              int c = _args._a0;
              return f0(c);
            },
            [&](const typename Regexp::Eps _args) -> T1 { return f1; },
            [&](const typename Regexp::Cat _args) -> T1 {
              std::shared_ptr<typename Regexp::regexp> r2 = _args._a0;
              std::shared_ptr<typename Regexp::regexp> r3 = _args._a1;
              return f2(r2, regexp_rec<T1>(f, f0, f1, f2, f3, f4, f5, r2), r3,
                        regexp_rec<T1>(f, f0, f1, f2, f3, f4, f5, r3));
            },
            [&](const typename Regexp::Alt _args) -> T1 {
              std::shared_ptr<typename Regexp::regexp> r2 = _args._a0;
              std::shared_ptr<typename Regexp::regexp> r3 = _args._a1;
              return f3(r2, regexp_rec<T1>(f, f0, f1, f2, f3, f4, f5, r2), r3,
                        regexp_rec<T1>(f, f0, f1, f2, f3, f4, f5, r3));
            },
            [&](const typename Regexp::Zero _args) -> T1 { return f4; },
            [&](const typename Regexp::Star _args) -> T1 {
              std::shared_ptr<typename Regexp::regexp> r0 = _args._a0;
              return f5(r0, regexp_rec<T1>(f, f0, f1, f2, f3, f4, f5, r0));
            }},
        *r);
  }

  static bool regexp_eq(const std::shared_ptr<typename Regexp::regexp> r,
                        const std::shared_ptr<typename Regexp::regexp> x);

  static std::shared_ptr<typename Regexp::regexp>
  OptCat(const std::shared_ptr<typename Regexp::regexp> r2,
         const std::shared_ptr<typename Regexp::regexp> r3);

  static std::shared_ptr<typename Regexp::regexp>
  OptAlt(const std::shared_ptr<typename Regexp::regexp> r2,
         const std::shared_ptr<typename Regexp::regexp> r3);

  static std::shared_ptr<typename Regexp::regexp>
  null(const std::shared_ptr<typename Regexp::regexp> r);

  static bool accepts_null(const std::shared_ptr<typename Regexp::regexp> r);

  static std::shared_ptr<typename Regexp::regexp>
  deriv(const std::shared_ptr<typename Regexp::regexp> r, const int c);

  static std::shared_ptr<typename Regexp::regexp>
  derivs(const std::shared_ptr<typename Regexp::regexp> r,
         const std::shared_ptr<typename List::list<int>> cs);

  static bool deriv_parse(const std::shared_ptr<typename Regexp::regexp> r,
                          const std::shared_ptr<typename List::list<int>> cs);

  static bool NullEpsOrZero(const std::shared_ptr<typename Regexp::regexp> r);

  static bool parse(const std::shared_ptr<typename Regexp::regexp> r,
                    const std::shared_ptr<typename List::list<int>> cs);

  static bool parse_bool(const std::shared_ptr<typename Regexp::regexp> r,
                         const std::shared_ptr<typename List::list<int>> cs);

  static inline const std::shared_ptr<typename Regexp::regexp> r1 =
      Regexp::Cat::make(Regexp::Star::make(Regexp::Char::make(0)),
                        Regexp::Char::make(1));

  static inline const std::shared_ptr<typename List::list<int>> s1 =
      List::cons<int>::make(0,
                            List::cons<int>::make(1, List::nil<int>::make()));

  static inline const std::shared_ptr<typename List::list<int>> s2 =
      List::cons<int>::make(1, List::nil<int>::make());

  static inline const std::shared_ptr<typename List::list<int>> s3 =
      List::cons<int>::make(
          0, List::cons<int>::make(
                 0, List::cons<int>::make(1, List::nil<int>::make())));

  static inline const std::shared_ptr<typename List::list<int>> s4 =
      List::cons<int>::make(0, List::nil<int>::make());
};
