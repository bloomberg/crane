#include <any>
#include <fstream>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>
#include <vector.h>
#include <vector>

int vectest::test1(const int _x) {
  std::vector<int> v = {};
  v.push_back(3);
  v.push_back(2);
  v.push_back(7);
  int x = v.size();
  v.pop_back();
  int y = v.size();
  return x - y;
}

std::vector<int> vectest::test2(const int _x) {
  std::vector<int> v = {};
  v.push_back(12);
  v.push_back(23);
  v.pop_back();
  v.push_back(3);
  int x = v.size();
  v.push_back(x);
  int y = v.at(2);
  v.push_back(98);
  v.push_back(y);
  return v;
}
