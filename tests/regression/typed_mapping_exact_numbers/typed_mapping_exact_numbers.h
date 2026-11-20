#pragma once

#include <boost/multiprecision/cpp_int.hpp>

struct TypedMappingExactNumbers {
  static boost::multiprecision::cpp_int
  factorial(const boost::multiprecision::cpp_int &n);
  /// Larger than 2^64.
  [[gnu::used]] static inline const boost::multiprecision::cpp_int big =
      boost::multiprecision::cpp_int("100000000000000000000");
  static bool exceeds_big(const boost::multiprecision::cpp_int &n);
  static boost::multiprecision::cpp_int
  predecessor(const boost::multiprecision::cpp_int &n);
  static boost::multiprecision::cpp_int
  sum3(const boost::multiprecision::cpp_int &a,
       const boost::multiprecision::cpp_int &b,
       const boost::multiprecision::cpp_int &c);
};
