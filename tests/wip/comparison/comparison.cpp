#include <algorithm>
#include <any>
#include <comparison.h>
#include <functional>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int Comparison::cmp_to_nat(const std::shared_ptr<Comparison::cmp> &c) {
  return std::visit(
      Overloaded{
          [](const typename Comparison::cmp::CmpLt _args) -> unsigned int {
            return 0u;
          },
          [](const typename Comparison::cmp::CmpEq _args) -> unsigned int {
            return 1u;
          },
          [](const typename Comparison::cmp::CmpGt _args) -> unsigned int {
            return 2u;
          }},
      c->v());
}

std::shared_ptr<Comparison::cmp>
Comparison::compare_nats(const unsigned int a, const unsigned int b) {
  return std::visit(
      Overloaded{[](const typename Bool0::bool0::true0 _args)
                     -> std::shared_ptr<Comparison::cmp> {
                   return cmp::ctor::CmpLt_();
                 },
                 [&](const typename Bool0::bool0::false0 _args)
                     -> std::shared_ptr<Comparison::cmp> {
                   return std::visit(
                       Overloaded{[](const typename Bool0::bool0::true0 _args)
                                      -> std::shared_ptr<Comparison::cmp> {
                                    return cmp::ctor::CmpEq_();
                                  },
                                  [](const typename Bool0::bool0::false0 _args)
                                      -> std::shared_ptr<Comparison::cmp> {
                                    return cmp::ctor::CmpGt_();
                                  }},
                       (a == b)->v());
                 }},
      (a < b)->v());
}

unsigned int Comparison::max_nat(const unsigned int a, const unsigned int b) {
  return std::visit(
      Overloaded{
          [&](const typename Comparison::cmp::CmpLt _args) -> unsigned int {
            return b;
          },
          [&](const typename Comparison::cmp::CmpEq _args) -> unsigned int {
            return a;
          },
          [&](const typename Comparison::cmp::CmpGt _args) -> unsigned int {
            return a;
          }},
      compare_nats(a, b)->v());
}

unsigned int Comparison::min_nat(const unsigned int a, const unsigned int b) {
  return std::visit(
      Overloaded{
          [&](const typename Comparison::cmp::CmpLt _args) -> unsigned int {
            return a;
          },
          [&](const typename Comparison::cmp::CmpEq _args) -> unsigned int {
            return a;
          },
          [&](const typename Comparison::cmp::CmpGt _args) -> unsigned int {
            return b;
          }},
      compare_nats(a, b)->v());
}

unsigned int Comparison::clamp(const unsigned int val0, const unsigned int lo,
                               const unsigned int hi) {
  return std::visit(
      Overloaded{
          [&](const typename Comparison::cmp::CmpLt _args) -> unsigned int {
            return lo;
          },
          [&](const typename Comparison::cmp::CmpEq _args) -> unsigned int {
            return std::visit(
                Overloaded{[&](const typename Comparison::cmp::CmpLt _args)
                               -> unsigned int { return val0; },
                           [&](const typename Comparison::cmp::CmpEq _args)
                               -> unsigned int { return val0; },
                           [&](const typename Comparison::cmp::CmpGt _args)
                               -> unsigned int { return hi; }},
                compare_nats(val0, hi)->v());
          },
          [&](const typename Comparison::cmp::CmpGt _args) -> unsigned int {
            return std::visit(
                Overloaded{[&](const typename Comparison::cmp::CmpLt _args)
                               -> unsigned int { return val0; },
                           [&](const typename Comparison::cmp::CmpEq _args)
                               -> unsigned int { return val0; },
                           [&](const typename Comparison::cmp::CmpGt _args)
                               -> unsigned int { return hi; }},
                compare_nats(val0, hi)->v());
          }},
      compare_nats(val0, lo)->v());
}

std::shared_ptr<Comparison::cmp>
Comparison::flip_cmp(const std::shared_ptr<Comparison::cmp> &c) {
  return std::visit(Overloaded{[](const typename Comparison::cmp::CmpLt _args)
                                   -> std::shared_ptr<Comparison::cmp> {
                                 return cmp::ctor::CmpGt_();
                               },
                               [](const typename Comparison::cmp::CmpEq _args)
                                   -> std::shared_ptr<Comparison::cmp> {
                                 return cmp::ctor::CmpEq_();
                               },
                               [](const typename Comparison::cmp::CmpGt _args)
                                   -> std::shared_ptr<Comparison::cmp> {
                                 return cmp::ctor::CmpLt_();
                               }},
                    c->v());
}
