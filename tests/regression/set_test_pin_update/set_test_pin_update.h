#ifndef INCLUDED_SET_TEST_PIN_UPDATE
#define INCLUDED_SET_TEST_PIN_UPDATE

#include <utility>

struct SetTestPinUpdate {
  struct state {
    uint64_t acc;
    bool test_pin;

    // ACCESSORS
    state clone() const { return state{this->acc, this->test_pin}; }
  };

  static state set_test_pin(const state &s, bool v);
  static inline const uint64_t t = []() {
    return []() {
      state s_ = set_test_pin(state{UINT64_C(6), false}, true);
      return (s_.acc + (std::move(s_).test_pin ? UINT64_C(1) : UINT64_C(0)));
    }();
  }();
};

#endif // INCLUDED_SET_TEST_PIN_UPDATE
