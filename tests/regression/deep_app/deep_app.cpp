#include <deep_app.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// Tail-recursive builder — loopified.
std::shared_ptr<DeepApp::mylist<unsigned int>>
DeepApp::build(const unsigned int n,
               std::shared_ptr<DeepApp::mylist<unsigned int>> acc) {
  std::shared_ptr<DeepApp::mylist<unsigned int>> _result;
  std::shared_ptr<DeepApp::mylist<unsigned int>> _loop_acc = acc;
  unsigned int _loop_n = n;
  bool _continue = true;
  while (_continue) {
    if (_loop_n <= 0) {
      {
        _result = std::move(_loop_acc);
        _continue = false;
      }
    } else {
      unsigned int n_ = _loop_n - 1;
      {
        std::shared_ptr<DeepApp::mylist<unsigned int>> _next_acc =
            mylist<unsigned int>::mycons(_loop_n, _loop_acc);
        unsigned int _next_n = std::move(n_);
        _loop_acc = std::move(_next_acc);
        _loop_n = std::move(_next_n);
        continue;
      }
    }
  }
  return _result;
}

/// Identity map to force traversal.
std::shared_ptr<DeepApp::mylist<unsigned int>>
DeepApp::map_id(const std::shared_ptr<DeepApp::mylist<unsigned int>> &l) {
  return map<unsigned int, unsigned int>([](unsigned int x) { return x; }, l);
}

/// Append two lists.
std::shared_ptr<DeepApp::mylist<unsigned int>> DeepApp::append_lists(
    const std::shared_ptr<DeepApp::mylist<unsigned int>> &_x0,
    const std::shared_ptr<DeepApp::mylist<unsigned int>> &_x1) {
  return app<unsigned int>(_x0, _x1);
}

__attribute__((pure)) unsigned int
DeepApp::head_or_zero(const std::shared_ptr<DeepApp::mylist<unsigned int>> &l) {
  return std::visit(
      Overloaded{[](const typename DeepApp::mylist<unsigned int>::Mynil _args)
                     -> unsigned int { return 0u; },
                 [](const typename DeepApp::mylist<unsigned int>::Mycons _args)
                     -> unsigned int { return _args.d_a0; }},
      l->v());
}
