#ifndef INCLUDED_SET_TEST_PIN_UPDATE
#define INCLUDED_SET_TEST_PIN_UPDATE

#include <cstdint>

struct SetTestPinUpdate {
  struct state {
    uint64_t acc;
    bool test_pin;
  };

  static state set_test_pin(const state &s, bool v);
  static constexpr uint64_t t = UINT64_C(7);
};

#endif // INCLUDED_SET_TEST_PIN_UPDATE
