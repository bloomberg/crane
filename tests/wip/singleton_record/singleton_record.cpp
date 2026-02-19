#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <singleton_record.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int
SingletonRecord::value(const std::shared_ptr<SingletonRecord::wrapper> &w) {
  return w;
}

unsigned int
SingletonRecord::get_value(const std::shared_ptr<SingletonRecord::wrapper> &w) {
  return w;
}

unsigned int SingletonRecord::get_value2(
    const std::shared_ptr<SingletonRecord::wrapper> &w) {
  return w;
}

unsigned int
SingletonRecord::unwrap(const std::shared_ptr<SingletonRecord::wrapper> &w) {
  return w;
}

std::shared_ptr<SingletonRecord::wrapper> SingletonRecord::double_wrapped(
    const std::shared_ptr<SingletonRecord::wrapper> &w) {
  return (2u * w);
}

unsigned int
SingletonRecord::fn(const std::shared_ptr<SingletonRecord::fn_wrapper> &f,
                    const unsigned int _x0) {
  return f(_x0);
}

unsigned int SingletonRecord::apply_wrapped(
    const std::shared_ptr<SingletonRecord::fn_wrapper> &w,
    const unsigned int _x0) {
  return w(_x0);
}
