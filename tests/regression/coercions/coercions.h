#ifndef INCLUDED_COERCIONS
#define INCLUDED_COERCIONS

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct Coercions {
  __attribute__((pure)) static unsigned int bool_to_nat(const bool &b);
  __attribute__((pure)) static unsigned int add_bool(const unsigned int &n,
                                                     const bool &b);
  static inline const unsigned int test_add_true = add_bool(5u, true);
  static inline const unsigned int test_add_false = add_bool(5u, false);

  struct Wrapper {
    unsigned int unwrap;

    __attribute__((pure)) Wrapper *operator->() { return this; }

    __attribute__((pure)) const Wrapper *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) Wrapper clone() const {
      return Wrapper{[](auto &&__v) -> unsigned int {
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
      }((*this).unwrap)};
    }
  };

  __attribute__((pure)) static unsigned int double_wrapped(const Wrapper &w);
  static inline const unsigned int test_double_wrapped =
      double_wrapped(Wrapper{7u});

  struct BoolBox {
    bool unbox;

    __attribute__((pure)) BoolBox *operator->() { return this; }

    __attribute__((pure)) const BoolBox *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) BoolBox clone() const {
      return BoolBox{[](auto &&__v) -> bool {
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
      }((*this).unbox)};
    }
  };

  __attribute__((pure)) static unsigned int add_boolbox(const unsigned int &n,
                                                        const BoolBox &bb);
  static inline const unsigned int test_add_boolbox =
      add_boolbox(10u, BoolBox{true});

  struct Transform {
    std::function<unsigned int(unsigned int)> apply_transform;

    __attribute__((pure)) Transform *operator->() { return this; }

    __attribute__((pure)) const Transform *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) Transform clone() const {
      return Transform{(*(this)).apply_transform};
    }
  };

  static inline const Transform double_transform =
      Transform{[](const unsigned int &n) { return (n + n); }};
  static inline const unsigned int test_fun_coercion =
      double_transform.apply_transform(5u);
};

#endif // INCLUDED_COERCIONS
