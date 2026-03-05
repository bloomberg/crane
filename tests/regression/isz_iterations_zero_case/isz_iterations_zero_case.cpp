#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <isz_iterations_zero_case.h>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int IszIterationsZeroCase::isz_iterations(const unsigned int v) {
  if ((v == 0)) {
    return ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1);
  } else {
    return (
        ((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1) -
          v) > ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1) +
                1)
             ? 0
             : (((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1) -
                v)));
  }
}
