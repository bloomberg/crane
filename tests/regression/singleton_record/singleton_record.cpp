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
#include <variant>

unsigned int
SingletonRecord::value(const std::shared_ptr<SingletonRecord::wrapper> &w) {
  return w->value;
}

unsigned int
SingletonRecord::get_value(const std::shared_ptr<SingletonRecord::wrapper> &w) {
  return w->value;
}

unsigned int SingletonRecord::get_value2(
    const std::shared_ptr<SingletonRecord::wrapper> &w) {
  return w->value;
}

unsigned int
SingletonRecord::unwrap(const std::shared_ptr<SingletonRecord::wrapper> &w) {
  return w->value;
}

std::shared_ptr<SingletonRecord::wrapper>
SingletonRecord::double_wrapped(std::shared_ptr<SingletonRecord::wrapper> w) {
  return std::make_shared<SingletonRecord::wrapper>(
      wrapper{(2u * std::move(w)->value)});
}

unsigned int
SingletonRecord::fn(const std::shared_ptr<SingletonRecord::fn_wrapper> &f,
                    const unsigned int _x0) {
  return f->fn(_x0);
}

unsigned int SingletonRecord::apply_wrapped(
    const std::shared_ptr<SingletonRecord::fn_wrapper> &w,
    const unsigned int n) {
  return w->fn(n);
}
