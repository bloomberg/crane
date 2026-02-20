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
SingletonRecord::value(std::shared_ptr<SingletonRecord::wrapper> w) {
  return std::move(w);
}

unsigned int
SingletonRecord::get_value(std::shared_ptr<SingletonRecord::wrapper> w) {
  return std::move(w);
}

unsigned int
SingletonRecord::get_value2(std::shared_ptr<SingletonRecord::wrapper> w) {
  return std::move(w);
}

unsigned int
SingletonRecord::unwrap(std::shared_ptr<SingletonRecord::wrapper> w) {
  return std::move(w);
}

std::shared_ptr<SingletonRecord::wrapper> SingletonRecord::double_wrapped(
    const std::shared_ptr<SingletonRecord::wrapper> &w) {
  return (2u * w);
}

unsigned int
SingletonRecord::fn(const std::shared_ptr<SingletonRecord::fn_wrapper> &f,
                    const unsigned int _x0) {
  return f(std::move(_x0));
}

unsigned int SingletonRecord::apply_wrapped(
    const std::shared_ptr<SingletonRecord::fn_wrapper> &w,
    const unsigned int _x0) {
  return w(std::move(_x0));
}
