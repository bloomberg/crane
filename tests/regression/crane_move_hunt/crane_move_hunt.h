#ifndef INCLUDED_CRANE_MOVE_HUNT
#define INCLUDED_CRANE_MOVE_HUNT

#include <memory>
#include <optional>
#include <toy_helpers.h>
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

template <typename T> struct is_optional : std::false_type {};

template <typename T> struct is_optional<std::optional<T>> : std::true_type {
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
      if constexpr (requires { x.clone(); }) {
        return std::make_unique<Inner>(x.clone());
      } else if constexpr (std::is_same_v<Inner, SourceBare>) {
        if constexpr (requires { x.clone(); }) {
          return std::make_unique<Inner>(x.clone());
        } else {
          return std::make_unique<Inner>(x);
        }
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x.template clone_as<Inner>());
      } else {
        if constexpr (requires { x.clone(); }) {
          return std::make_unique<Inner>(x.clone());
        } else {
          return std::make_unique<Inner>(x);
        }
      }
    }
  } else if constexpr (is_optional<TargetBare>::value) {
    using Inner = typename is_optional<TargetBare>::element_type;
    if constexpr (is_optional<SourceBare>::value) {
      if (!x)
        return std::nullopt;
      return Target{clone_as_value<Inner>(*x)};
    } else {
      return Target{clone_as_value<Inner>(x)};
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
      if (!x)
        return Target{};
      if constexpr (requires { x->clone(); }) {
        return x->clone();
      } else {
        return *x;
      }
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else if constexpr (requires { x->clone(); }) {
      return x->clone();
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

struct CraneMoveHunt {
  struct box {
    unsigned int payload;
    bool enabled;

    __attribute__((pure)) box *operator->() { return this; }

    __attribute__((pure)) const box *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) box clone() const {
      return box{clone_as_value<unsigned int>((*(this)).payload),
                 clone_as_value<bool>((*(this)).enabled)};
    }
  };

  struct state {
    box core;
    box cursor;
    bool visible;

    __attribute__((pure)) state *operator->() { return this; }

    __attribute__((pure)) const state *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) state clone() const {
      return state{clone_as_value<box>((*(this)).core),
                   clone_as_value<box>((*(this)).cursor),
                   clone_as_value<bool>((*(this)).visible)};
    }
  };

  __attribute__((pure)) static box clone_box(const box &b);
  __attribute__((pure)) static box keep_box(box b);
  __attribute__((pure)) static unsigned int use_state(const state &s);
  __attribute__((pure)) static state render_state(const state &s);
  __attribute__((pure)) static unsigned int sound_state(const state &before,
                                                        const state &after);
  __attribute__((pure)) static state resolve_state(const state &s);
  __attribute__((pure)) static std::pair<bool, state>
  handle_state(const state &s);
  static inline const box initial_box = box{41u, true};
  static inline const box other_box = box{1u, false};
  static inline const state initial_state = state{initial_box, other_box, true};
  static inline const box record_constant = []() {
    box b = keep_box(initial_box);
    box b1 = clone_box(b);
    box b2 = clone_box(b);
    if (keep_box(b).enabled) {
      if (b.enabled) {
        return b2;
      } else {
        return b1;
      }
    } else {
      return b1;
    }
  }();
  __attribute__((pure)) static box record_function(const box &b0);
  static inline const state state_constant = []() {
    state s1 = render_state(initial_state);
    state s2 = resolve_state(s1);
    return render_state(s2);
  }();
  __attribute__((pure)) static state state_function(const state &s0);
  __attribute__((pure)) static state match_reuse(const state &s0);
};

void tick(CraneMoveHunt::state s);
CraneMoveHunt::state effect_frame(const CraneMoveHunt::state &s0);
CraneMoveHunt::state effect_pair_frame(const CraneMoveHunt::state &s0);
__attribute__((pure)) CraneMoveHunt::state
pure_pair_frame(const CraneMoveHunt::state &s0);
const CraneMoveHunt::box exported_record_constant =
    CraneMoveHunt::record_constant;
const CraneMoveHunt::box exported_record_function =
    CraneMoveHunt::record_function(CraneMoveHunt::initial_box);
const CraneMoveHunt::state exported_state_constant =
    CraneMoveHunt::state_constant;
const CraneMoveHunt::state exported_state_function =
    CraneMoveHunt::state_function(CraneMoveHunt::initial_state);
const CraneMoveHunt::state exported_match_reuse =
    CraneMoveHunt::match_reuse(CraneMoveHunt::initial_state);
CraneMoveHunt::state exported_effect_frame();
CraneMoveHunt::state exported_effect_pair_frame();
const CraneMoveHunt::state exported_pure_pair_frame =
    pure_pair_frame(CraneMoveHunt::initial_state);
__attribute__((pure)) CraneMoveHunt::state
axiom_pair_frame(const CraneMoveHunt::state &s0);
const CraneMoveHunt::state exported_axiom_pair_frame =
    axiom_pair_frame(CraneMoveHunt::initial_state);
__attribute__((pure)) CraneMoveHunt::state
axiom_nat_pair_frame(const CraneMoveHunt::state &s0);
const CraneMoveHunt::state exported_axiom_nat_pair_frame =
    axiom_nat_pair_frame(CraneMoveHunt::initial_state);

#endif // INCLUDED_CRANE_MOVE_HUNT
