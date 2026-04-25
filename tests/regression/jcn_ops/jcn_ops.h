#ifndef INCLUDED_JCN_OPS
#define INCLUDED_JCN_OPS

#include <memory>
#include <type_traits>
#include <utility>

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
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_shared<T>(x->clone()) : nullptr;
  } else {
    return x;
  }
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

struct JcnOps {
  struct state {
    unsigned int acc;
    bool carry;
    bool test_pin;
    unsigned int pc;

    __attribute__((pure)) state *operator->() { return this; }

    __attribute__((pure)) const state *operator->() const { return this; }
  };

  __attribute__((pure)) static bool jcn_condition(const state &s,
                                                  const unsigned int &cond);
  __attribute__((pure)) static unsigned int
  addr12_of_nat(const unsigned int &n);
  __attribute__((pure)) static unsigned int pc_inc2(const state &s);
  __attribute__((pure)) static unsigned int page_of(const unsigned int &p);
  __attribute__((pure)) static unsigned int page_base(const unsigned int &p);
  __attribute__((pure)) static unsigned int base_for_next2(const state &s);
  __attribute__((pure)) static unsigned int
  branch_target(const state &s, const unsigned int &cond,
                const unsigned int &off);
  static inline const unsigned int test_branch_target =
      branch_target(state{0u, true, false, 300u}, 2u, 17u);
  static inline const bool check_carry_clear_gate =
      jcn_condition(state{1u, false, true, 0u}, 10u);
  static inline const bool check_nonzero_gate =
      jcn_condition(state{3u, false, true, 0u}, 12u);
  static inline const bool check_test_high =
      jcn_condition(state{1u, false, true, 0u}, 9u);
  static inline const bool check_test_low =
      jcn_condition(state{1u, false, false, 0u}, 1u);
  static inline const bool check_zero_gate =
      jcn_condition(state{0u, false, true, 0u}, 4u);
  static inline const bool test_condition =
      (check_carry_clear_gate &&
       (check_nonzero_gate &&
        (check_test_high && (check_test_low && check_zero_gate))));
  static inline const unsigned int JCN_JNT = 1u;
  static inline const unsigned int JCN_JC = 2u;
  static inline const unsigned int JCN_JZ = 4u;
  static inline const unsigned int JCN_JT = 9u;
  static inline const unsigned int JCN_JNC = 10u;
  static inline const unsigned int JCN_JNZ = 12u;
  static inline const unsigned int test_constants = []() {
    return []() {
      state s = state{0u, true, false, 0u};
      return (([&]() -> unsigned int {
                if (jcn_condition(s, JCN_JC)) {
                  return 1u;
                } else {
                  return 0u;
                }
              }() + [&]() -> unsigned int {
                if (jcn_condition(s, JCN_JZ)) {
                  return 1u;
                } else {
                  return 0u;
                }
              }()) +
                  [&]() -> unsigned int {
        if (jcn_condition(s, JCN_JNT)) {
          return 1u;
        } else {
          return 0u;
        }
      }());
    }();
  }();
  static inline const std::pair<std::pair<unsigned int, bool>, unsigned int> t =
      std::make_pair(std::make_pair(test_branch_target, test_condition),
                     test_constants);
};

#endif // INCLUDED_JCN_OPS
