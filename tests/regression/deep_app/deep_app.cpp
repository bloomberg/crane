#include <deep_app.h>

/// Tail-recursive builder — loopified.
__attribute__((pure)) DeepApp::mylist<unsigned int>
DeepApp::build(unsigned int n, DeepApp::mylist<unsigned int> acc) {
  DeepApp::mylist<unsigned int> _result;
  DeepApp::mylist<unsigned int> _loop_acc = std::move(acc);
  unsigned int _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      _result = std::move(_loop_acc);
      break;
    } else {
      unsigned int n_ = _loop_n - 1;
      DeepApp::mylist<unsigned int> _next_acc =
          mylist<unsigned int>::mycons(_loop_n, std::move(_loop_acc));
      unsigned int _next_n = n_;
      _loop_acc = std::move(_next_acc);
      _loop_n = std::move(_next_n);
    }
  }
  return _result;
}

/// Identity map to force traversal.
__attribute__((pure)) DeepApp::mylist<unsigned int>
DeepApp::map_id(const DeepApp::mylist<unsigned int> &l) {
  return map<unsigned int, unsigned int>([](unsigned int x) { return x; }, l);
}

/// Append two lists.
__attribute__((pure)) DeepApp::mylist<unsigned int>
DeepApp::append_lists(const DeepApp::mylist<unsigned int> &_x0,
                      const DeepApp::mylist<unsigned int> &_x1) {
  return app<unsigned int>(_x0, _x1);
}

__attribute__((pure)) unsigned int
DeepApp::head_or_zero(const DeepApp::mylist<unsigned int> &l) {
  if (std::holds_alternative<typename DeepApp::mylist<unsigned int>::Mynil>(
          l.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename DeepApp::mylist<unsigned int>::Mycons>(l.v());
    return d_a0;
  }
}
