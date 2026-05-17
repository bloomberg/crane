#include "deep_app.h"

/// Tail-recursive builder — loopified.
DeepApp::mylist<uint64_t> DeepApp::build(uint64_t n,
                                         DeepApp::mylist<uint64_t> acc) {
  DeepApp::mylist<uint64_t> _result;
  DeepApp::mylist<uint64_t> _loop_acc = std::move(acc);
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      _result = std::move(_loop_acc);
      break;
    } else {
      uint64_t n_ = _loop_n - 1;
      uint64_t _next_n = n_;
      _loop_acc = mylist<uint64_t>::mycons(_loop_n, std::move(_loop_acc));
      _loop_n = _next_n;
    }
  }
  return _result;
}

/// Identity map to force traversal.
DeepApp::mylist<uint64_t> DeepApp::map_id(const DeepApp::mylist<uint64_t> &l) {
  return map<uint64_t, uint64_t>([](uint64_t x) { return x; }, l);
}

/// Append two lists.
DeepApp::mylist<uint64_t>
DeepApp::append_lists(const DeepApp::mylist<uint64_t> &_x0,
                      const DeepApp::mylist<uint64_t> &_x1) {
  return app<uint64_t>(_x0, _x1);
}

uint64_t DeepApp::head_or_zero(const DeepApp::mylist<uint64_t> &l) {
  if (std::holds_alternative<typename DeepApp::mylist<uint64_t>::Mynil>(
          l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename DeepApp::mylist<uint64_t>::Mycons>(l.v());
    return a0;
  }
}
