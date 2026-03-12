#include <kbp_multibit_default.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<KbpMultibitDefault::state> KbpMultibitDefault::execute_kbp(
    const std::shared_ptr<KbpMultibitDefault::state> &s) {
  unsigned int result;
  if (s->acc <= 0) {
    result = 0u;
  } else {
    unsigned int n = s->acc - 1;
    if (n <= 0) {
      result = 1u;
    } else {
      unsigned int n0 = n - 1;
      if (n0 <= 0) {
        result = 2u;
      } else {
        unsigned int n1 = n0 - 1;
        if (n1 <= 0) {
          result = 15u;
        } else {
          unsigned int n2 = n1 - 1;
          if (n2 <= 0) {
            result = 3u;
          } else {
            unsigned int n3 = n2 - 1;
            if (n3 <= 0) {
              result = 15u;
            } else {
              unsigned int n4 = n3 - 1;
              if (n4 <= 0) {
                result = 15u;
              } else {
                unsigned int n5 = n4 - 1;
                if (n5 <= 0) {
                  result = 15u;
                } else {
                  unsigned int n6 = n5 - 1;
                  if (n6 <= 0) {
                    result = 4u;
                  } else {
                    unsigned int _x = n6 - 1;
                    result = 15u;
                  }
                }
              }
            }
          }
        }
      }
    }
  }
  return std::make_shared<KbpMultibitDefault::state>(state{std::move(result)});
}
