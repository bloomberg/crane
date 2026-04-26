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

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_unique<T>(x->clone()) : nullptr;
  } else {
    return x ? std::make_unique<T>(*x) : nullptr;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using T = std::remove_cvref_t<Target>;
  using S = std::remove_cvref_t<Source>;
  if constexpr (requires(const S &s) {
                  s.has_value();
                  *s;
                }) {
    if (!x.has_value())
      return T{};
    using TInner = std::remove_cvref_t<decltype(*std::declval<const T &>())>;
    return T{clone_as_value<TInner>(*x)};
  } else if constexpr (std::is_same_v<T, S>) {
    if constexpr (is_unique_ptr<T>::value) {
      return clone_value(x);
    } else if constexpr (requires { x.clone(); }) {
      return x.clone();
    } else {
      return x;
    }
  } else if constexpr (is_unique_ptr<S>::value) {
    if (!x)
      return T{};
    return clone_as_value<T>(*x);
  } else if constexpr (is_unique_ptr<T>::value) {
    using Inner = typename is_unique_ptr<T>::element_type;
    return std::make_unique<Inner>(clone_as_value<Inner>(x));
  } else {
    return T(x);
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
      return box{(*(this)).payload, (*(this)).enabled};
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
      return state{(*(this)).core, (*(this)).cursor, (*(this)).visible};
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
