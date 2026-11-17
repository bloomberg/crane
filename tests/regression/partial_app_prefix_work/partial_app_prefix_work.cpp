#include "partial_app_prefix_work.h"

uint64_t PartialAppPrefixWork::mk(const List<crane::fn<uint64_t(uint64_t)>> &fs,
                                  uint64_t x0_) {
  return fs.template fold_right<crane::fn<uint64_t(uint64_t)>>(
      [](crane::fn<uint64_t(uint64_t)> _ec0,
         crane::fn<uint64_t(uint64_t)> _ec1) {
        return [=, _ec0 = std::move(_ec0), _ec1 = std::move(_ec1)](
            uint64_t _ec2) { return compose<uint64_t>(_ec0, _ec1, _ec2); };
      },
      [](uint64_t x) { return x; })(x0_);
}

/// Its body is a partial application of mk, which computes as well.
uint64_t
PartialAppPrefixWork::mk2(const List<crane::fn<uint64_t(uint64_t)>> &fs,
                          uint64_t x0_) {
  return mk(
      fs.template map<crane::fn<uint64_t(uint64_t)>>(
          [](crane::fn<uint64_t(uint64_t)> f) {
            return [=, f = std::move(f)](uint64_t x) { return f(f(x)); };
          }),
      x0_);
}

/// A let before the closure.
uint64_t PartialAppPrefixWork::shifted(
    uint64_t k, const List<crane::fn<uint64_t(uint64_t)>> &fs, uint64_t x0_) {
  crane::fn<uint64_t(uint64_t)> g =
      fs.template fold_right<crane::fn<uint64_t(uint64_t)>>(
          [](crane::fn<uint64_t(uint64_t)> _ec0,
             crane::fn<uint64_t(uint64_t)> _ec1) {
            return [=, _ec0 = std::move(_ec0), _ec1 = std::move(_ec1)](
                uint64_t _ec2) { return compose<uint64_t>(_ec0, _ec1, _ec2); };
          },
          [](uint64_t x) { return x; });
  return g((x0_ + k));
}

uint64_t PartialAppPrefixWork::run(uint64_t n) {
  crane::fn<uint64_t(uint64_t)> g =
      fs3.template fold_right<crane::fn<uint64_t(uint64_t)>>(
          [](crane::fn<uint64_t(uint64_t)> _ec0,
             crane::fn<uint64_t(uint64_t)> _ec1) {
            return [=, _ec0 = std::move(_ec0), _ec1 = std::move(_ec1)](
                uint64_t _ec2) { return compose<uint64_t>(_ec0, _ec1, _ec2); };
          },
          [](uint64_t x) { return x; });
  crane::fn<uint64_t(uint64_t)> h =
      fs3.template fold_right<crane::fn<uint64_t(uint64_t)>>(
          [](crane::fn<uint64_t(uint64_t)> _ec0,
             crane::fn<uint64_t(uint64_t)> _ec1) {
            return [=, _ec0 = std::move(_ec0), _ec1 = std::move(_ec1)](
                uint64_t _ec2) { return compose<uint64_t>(_ec0, _ec1, _ec2); };
          },
          [](uint64_t x) { return x; });
  List<crane::fn<uint64_t(uint64_t)>> fs =
      fs3.template map<crane::fn<uint64_t(uint64_t)>>(
          [](crane::fn<uint64_t(uint64_t)> f) {
            return [=, f = std::move(f)](uint64_t x) { return f(f(x)); };
          });
  crane::fn<uint64_t(uint64_t)> k =
      fs.template fold_right<crane::fn<uint64_t(uint64_t)>>(
          [](crane::fn<uint64_t(uint64_t)> _ec0,
             crane::fn<uint64_t(uint64_t)> _ec1) {
            return [=, _ec0 = std::move(_ec0), _ec1 = std::move(_ec1)](
                uint64_t _ec2) { return compose<uint64_t>(_ec0, _ec1, _ec2); };
          },
          [](uint64_t x) { return x; });
  uint64_t k0 = UINT64_C(5);
  crane::fn<uint64_t(uint64_t)> g0 =
      fs3.template fold_right<crane::fn<uint64_t(uint64_t)>>(
          [](crane::fn<uint64_t(uint64_t)> _ec0,
             crane::fn<uint64_t(uint64_t)> _ec1) {
            return [=, _ec0 = std::move(_ec0), _ec1 = std::move(_ec1)](
                uint64_t _ec2) { return compose<uint64_t>(_ec0, _ec1, _ec2); };
          },
          [](uint64_t x) { return x; });
  crane::fn<uint64_t(uint64_t)> s =
      [=, g0 = std::move(g0)](uint64_t x) { return g0((x + k0)); };
  return (
      ListDef::seq(UINT64_C(0), n).template fold_left<uint64_t>(
          [=, g = std::move(g), h = std::move(h), k = std::move(k),
           s = std::move(s)](uint64_t acc,
                             uint64_t i) {
            return (((((acc + g(i)) + h(i)) + k(i)) + s(i)) + mk(fs3, i));
          },
          UINT64_C(0)) +
      ListDef::seq(UINT64_C(0), n).template map<uint64_t>(
          fs3.template fold_right<crane::fn<uint64_t(uint64_t)>>(
              [](crane::fn<uint64_t(uint64_t)> _ec0,
                 crane::fn<uint64_t(uint64_t)> _ec1) {
                return [=, _ec0 = std::move(_ec0), _ec1 = std::move(_ec1)](
                    uint64_t _ec2) {
                  return compose<uint64_t>(_ec0, _ec1, _ec2);
                };
              },
              [](uint64_t x) { return x; }))
          .template fold_left<uint64_t>(
          [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); },
          UINT64_C(0)));
}

List<uint64_t> ListDef::seq(uint64_t start, uint64_t len) {
  if (len <= 0) {
    return List<uint64_t>::nil();
  } else {
    uint64_t len0 = len - 1;
    return List<uint64_t>::cons(start, ListDef::seq((start + 1), len0));
  }
}
