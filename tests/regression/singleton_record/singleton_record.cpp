#include "singleton_record.h"

uint64_t SingletonRecord::get_value(const SingletonRecord::wrapper &w) {
  return w.value;
}

uint64_t SingletonRecord::get_value2(const SingletonRecord::wrapper &w) {
  return w.value;
}

uint64_t SingletonRecord::unwrap(const SingletonRecord::wrapper &w) {
  return w.value;
}

SingletonRecord::wrapper
SingletonRecord::double_wrapped(const SingletonRecord::wrapper &w) {
  return wrapper{(UINT64_C(2) * w.value)};
}

uint64_t SingletonRecord::apply_wrapped(const SingletonRecord::fn_wrapper &w,
                                        uint64_t n) {
  return w.fn(n);
}
