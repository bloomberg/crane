#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <option_tuple_wrapper.h>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

Node::shadow OptionTupleWrapper::pick(const bool b) {
  if (b) {
    return Node::shadow::TagA;
  } else {
    return Node::shadow::TagB;
  }
}
