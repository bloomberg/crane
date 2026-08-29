#include "kbp_multibit_default.h"

KbpMultibitDefault::state
KbpMultibitDefault::execute_kbp(const KbpMultibitDefault::state &s) {
  uint64_t result;
  if (s.acc <= 0) {
    result = UINT64_C(0);
  } else {
    uint64_t n = s.acc - 1;
    if (n <= 0) {
      result = UINT64_C(1);
    } else {
      uint64_t n0 = n - 1;
      if (n0 <= 0) {
        result = UINT64_C(2);
      } else {
        uint64_t n1 = n0 - 1;
        if (n1 <= 0) {
          result = UINT64_C(15);
        } else {
          uint64_t n2 = n1 - 1;
          if (n2 <= 0) {
            result = UINT64_C(3);
          } else {
            uint64_t n3 = n2 - 1;
            if (n3 <= 0) {
              result = UINT64_C(15);
            } else {
              uint64_t n4 = n3 - 1;
              if (n4 <= 0) {
                result = UINT64_C(15);
              } else {
                uint64_t n5 = n4 - 1;
                if (n5 <= 0) {
                  result = UINT64_C(15);
                } else {
                  uint64_t n6 = n5 - 1;
                  if (n6 <= 0) {
                    result = UINT64_C(4);
                  } else {
                    uint64_t _x = n6 - 1;
                    result = UINT64_C(15);
                  }
                }
              }
            }
          }
        }
      }
    }
  }
  return state{result};
}
