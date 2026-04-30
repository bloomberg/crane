#ifndef INCLUDED_SET_TEST_PIN_UPDATE
#define INCLUDED_SET_TEST_PIN_UPDATE

#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct SetTestPinUpdate {
  struct state {
    unsigned int acc;
    bool test_pin;

    // ACCESSORS
    state clone() const { return state{(*(this)).acc, (*(this)).test_pin}; }
  };

  static state set_test_pin(const state &s, bool v);
  static inline const unsigned int t = []() {
    return []() {
      state s_ = set_test_pin(state{6u, false}, true);
      return (s_.acc + (s_.test_pin ? 1u : 0u));
    }();
  }();
};

#endif // INCLUDED_SET_TEST_PIN_UPDATE
