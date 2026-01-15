#include <algorithm>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <top.h>
#include <utility>
#include <variant>

std::shared_ptr<List::list<unsigned int>> seq(const unsigned int start,
                                              const unsigned int len) {
  if (len <= 0) {
    return List::list<unsigned int>::ctor::nil_();
  } else {
    unsigned int len0 = len - 1;
    return List::list<unsigned int>::ctor::cons_(start, seq((start + 1), len0));
  }
}
