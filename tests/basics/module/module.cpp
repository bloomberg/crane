#include <algorithm>
#include <any>
#include <functional>
#include <iostream>
#include <memory>
#include <module.h>
#include <optional>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<Comparison::comparison> compare(const unsigned int n,
                                                const unsigned int m) {
  if (n <= 0) {
    if (m <= 0) {
      return Comparison::comparison::ctor::Eq_();
    } else {
      unsigned int _x = m - 1;
      return Comparison::comparison::ctor::Lt_();
    }
  } else {
    unsigned int n_ = n - 1;
    if (m <= 0) {
      return Comparison::comparison::ctor::Gt_();
    } else {
      unsigned int m_ = m - 1;
      return compare(n_, m_);
    }
  }
}

std::shared_ptr<Comparison::comparison>
NatOrdered::compare(const unsigned int _x0, const unsigned int _x1) {
  return ::compare(_x0, _x1);
}
