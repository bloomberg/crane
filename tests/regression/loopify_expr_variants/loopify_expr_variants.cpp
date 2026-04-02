#include <loopify_expr_variants.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) std::pair<unsigned int, unsigned int>
Nat::divmod(const unsigned int x, const unsigned int y, const unsigned int q,
            const unsigned int u) {
  std::pair<unsigned int, unsigned int> _result;
  unsigned int _loop_u = u;
  unsigned int _loop_q = q;
  unsigned int _loop_x = x;
  bool _continue = true;
  while (_continue) {
    if (_loop_x <= 0) {
      {
        _result = std::make_pair(_loop_q, _loop_u);
        _continue = false;
      }
    } else {
      unsigned int x_ = _loop_x - 1;
      if (_loop_u <= 0) {
        {
          unsigned int _next_u = y;
          unsigned int _next_q = (_loop_q + 1);
          unsigned int _next_x = std::move(x_);
          _loop_u = std::move(_next_u);
          _loop_q = std::move(_next_q);
          _loop_x = std::move(_next_x);
          continue;
        }
      } else {
        unsigned int u_ = _loop_u - 1;
        {
          unsigned int _next_u = std::move(u_);
          unsigned int _next_x = std::move(x_);
          _loop_u = std::move(_next_u);
          _loop_x = std::move(_next_x);
          continue;
        }
      }
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int Nat::div(const unsigned int x,
                                            const unsigned int y) {
  if (y <= 0) {
    return std::move(y);
  } else {
    unsigned int y_ = y - 1;
    return Nat::divmod(x, y_, 0u, y_).first;
  }
}
