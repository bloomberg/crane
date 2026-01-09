#include <algorithm>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <top.h>
#include <utility>
#include <variant>

std::shared_ptr<typename List::list<unsigned int>> seq(const unsigned int start,
                                                       const unsigned int len) {
  if (len <= 0) {
    return List::nil<unsigned int>::make();
  } else {
    unsigned int len0 = len - 1;
    return List::cons<unsigned int>::make(start, seq((start + 1), len0));
  }
}
