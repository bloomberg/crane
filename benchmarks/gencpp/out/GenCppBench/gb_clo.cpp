#include "gb_clo.h"

uint64_t GbClo::next(uint64_t s) {
  auto &&_once1 = ((s * UINT64_C(75)) + UINT64_C(74));
  auto &&_once2 = UINT64_C(65537);
  return (_once2 ? _once1 % _once2 : _once1);
}

List<uint64_t> GbClo::randoms(uint64_t n, uint64_t s) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  uint64_t _loop_s = s;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t n_ = _loop_n - 1;
      auto _cell = typename List<uint64_t>::Cons(_loop_s, nullptr);
      List<uint64_t> &_node =
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
      _loop_s = next(_loop_s);
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*_root);
}

List<crane::fn<uint64_t(uint64_t)>> GbClo::build(uint64_t n) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<crane::fn<uint64_t(uint64_t)>>> _root{};
  std::shared_ptr<List<crane::fn<uint64_t(uint64_t)>>> *_write = nullptr;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      auto _value = List<crane::fn<uint64_t(uint64_t)>>::nil();
      (_write ? *(*_write =
                      std::make_shared<List<crane::fn<uint64_t(uint64_t)>>>(
                          std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t m = _loop_n - 1;
      auto _cell =
          typename List<crane::fn<uint64_t(uint64_t)>>::Cons(
              [=](uint64_t x) {
                auto &&_once1 = ((x * UINT64_C(3)) + _loop_n);
                auto &&_once2 = UINT64_C(4093);
                return (_once2 ? _once1 % _once2 : _once1);
              },
              nullptr);
      List<crane::fn<uint64_t(uint64_t)>> &_node = (
          _write ? *(*_write =
                         std::make_shared<List<crane::fn<uint64_t(uint64_t)>>>(
                             std::move(_cell)))
                 : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename List<crane::fn<uint64_t(uint64_t)>>::Cons>(
              _node.v_mut())
              .l;
      _loop_n = m;
      continue;
    }
  }
  return std::move(*_root);
}

uint64_t GbClo::closures(uint64_t n, uint64_t rounds) {
  List<crane::fn<uint64_t(uint64_t)>> fs = build(n);
  crane::fn<uint64_t(uint64_t)> big =
      fs.template fold_right<crane::fn<uint64_t(uint64_t)>>(
          [](crane::fn<uint64_t(uint64_t)> _ec0,
             crane::fn<uint64_t(uint64_t)> _ec1) {
            return [=, _ec0 = std::move(_ec0), _ec1 = std::move(_ec1)](
                uint64_t _ec2) { return compose(_ec0, _ec1, _ec2); };
          },
          [](uint64_t x) { return x; });
  return ListDef::seq(UINT64_C(0), rounds).template fold_left<uint64_t>(
      [=, big = std::move(big), fs = std::move(fs)](uint64_t acc, uint64_t i) {
        return ((acc + big(i)) +
                fs.template fold_left<uint64_t>(
                    [](uint64_t a,
                       const crane::fn<uint64_t(uint64_t)> &f) { return f(a); },
                    i));
      },
      UINT64_C(0));
}

List<uint64_t> ListDef::seq(uint64_t start, uint64_t len) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  uint64_t _loop_len = len;
  uint64_t _loop_start = start;
  while (true) {
    if (_loop_len <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t len0 = _loop_len - 1;
      auto _cell = typename List<uint64_t>::Cons(_loop_start, nullptr);
      List<uint64_t> &_node =
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
      _loop_len = len0;
      _loop_start = (_loop_start + 1);
      continue;
    }
  }
  return std::move(*_root);
}
