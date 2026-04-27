#ifndef INCLUDED_PATHOLOGICAL_RECORD
#define INCLUDED_PATHOLOGICAL_RECORD

#include <any>
#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct PathologicalRecord {
  struct Rec {
    unsigned int f1;
    unsigned int f2;
    unsigned int f3;

    __attribute__((pure)) Rec *operator->() { return this; }

    __attribute__((pure)) const Rec *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) Rec clone() const {
      return Rec{[](auto &&__v) -> unsigned int {
                   if constexpr (
                       requires { __v ? 0 : 0; } && requires { *__v; } &&
                       requires { __v->clone(); } && requires { __v.get(); }) {
                     using _E = std::remove_cvref_t<decltype(*__v)>;
                     return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
                   } else if constexpr (requires { __v.clone(); }) {
                     return __v.clone();
                   } else {
                     return __v;
                   }
                 }((*this).f1),
                 [](auto &&__v) -> unsigned int {
                   if constexpr (
                       requires { __v ? 0 : 0; } && requires { *__v; } &&
                       requires { __v->clone(); } && requires { __v.get(); }) {
                     using _E = std::remove_cvref_t<decltype(*__v)>;
                     return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
                   } else if constexpr (requires { __v.clone(); }) {
                     return __v.clone();
                   } else {
                     return __v;
                   }
                 }((*this).f2),
                 [](auto &&__v) -> unsigned int {
                   if constexpr (
                       requires { __v ? 0 : 0; } && requires { *__v; } &&
                       requires { __v->clone(); } && requires { __v.get(); }) {
                     using _E = std::remove_cvref_t<decltype(*__v)>;
                     return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
                   } else if constexpr (requires { __v.clone(); }) {
                     return __v.clone();
                   } else {
                     return __v;
                   }
                 }((*this).f3)};
    }
  };

  __attribute__((pure)) static unsigned int hof_access(const Rec &r);
  __attribute__((pure)) static unsigned int nested_lets(const Rec &r);
  __attribute__((pure)) static unsigned int
  conditional_access(const Rec &r, const bool &flag);
  __attribute__((pure)) static unsigned int countdown(const unsigned int &n,
                                                      const Rec &r);
  __attribute__((pure)) static unsigned int double_match(const Rec &r1,
                                                         const Rec &r2);
  __attribute__((pure)) static unsigned int
  closure_over_fields(const Rec &r, const unsigned int &x);
  static inline const unsigned int use_closure =
      closure_over_fields(Rec{1u, 2u, 3u}, 10u);
  __attribute__((pure)) static unsigned int guarded_pattern(const Rec &r);

  struct BigRec {
    unsigned int bf1;
    unsigned int bf2;
    unsigned int bf3;
    unsigned int bf4;
    unsigned int bf5;

    __attribute__((pure)) BigRec *operator->() { return this; }

    __attribute__((pure)) const BigRec *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) BigRec clone() const {
      return BigRec{
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).bf1),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).bf2),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).bf3),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).bf4),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).bf5)};
    }
  };

  __attribute__((pure)) static unsigned int scrambled_access(const BigRec &r);
  __attribute__((pure)) static unsigned int repeated_access(const BigRec &r);
  static inline const unsigned int test1 = hof_access(Rec{1u, 2u, 3u});
  static inline const unsigned int test2 = nested_lets(Rec{4u, 5u, 6u});
  static inline const unsigned int test3 =
      double_match(Rec{1u, 2u, 3u}, Rec{4u, 5u, 6u});
};

#endif // INCLUDED_PATHOLOGICAL_RECORD
