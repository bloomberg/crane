#include <algorithm>
#include <functional>
#include <iostream>
#include <memory>
#include <module.h>
#include <optional>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<typename Comparison::comparison> compare(const unsigned int n,
                                                         const unsigned int m) {
  if (n <= 0) {
    if (m <= 0) {
      return Comparison::Eq::make();
    } else {
      unsigned int _x = m - 1;
      return Comparison::Lt::make();
    }
  } else {
    unsigned int n_ = n - 1;
    if (m <= 0) {
      return Comparison::Gt::make();
    } else {
      unsigned int m_ = m - 1;
      return compare(n_, m_);
    }
  }
}
