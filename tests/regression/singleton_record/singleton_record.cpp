#include <singleton_record.h>

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>

__attribute__((pure)) unsigned int
SingletonRecord::get_value(const SingletonRecord::wrapper &w) {
  return w.value;
}

__attribute__((pure)) unsigned int
SingletonRecord::get_value2(const SingletonRecord::wrapper &w) {
  return w.value;
}

__attribute__((pure)) unsigned int
SingletonRecord::unwrap(const SingletonRecord::wrapper &w) {
  return w.value;
}

__attribute__((pure)) SingletonRecord::wrapper
SingletonRecord::double_wrapped(const SingletonRecord::wrapper &w) {
  return wrapper{(2u * w.value)};
}

__attribute__((pure)) unsigned int
SingletonRecord::apply_wrapped(const SingletonRecord::fn_wrapper &w,
                               const unsigned int &n) {
  return w.fn(n);
}
