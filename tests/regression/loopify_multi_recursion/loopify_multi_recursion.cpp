#include <loopify_multi_recursion.h>

__attribute__((pure)) unsigned int
LoopifyMultiRecursion::mixed_arith_fuel(const unsigned int &fuel,
                                        const unsigned int &n) {
  struct _Enter {
    const unsigned int n;
    const unsigned int fuel;
  };

  struct _Call1 {
    const unsigned int _s0;
    const unsigned int _s1;
    const unsigned int _s2;
    const unsigned int _s3;
  };

  struct _Call2 {
    unsigned int _s0;
    const unsigned int _s1;
    const unsigned int _s2;
  };

  struct _Call3 {
    unsigned int _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &n = _f.n;
      const unsigned int &fuel = _f.fuel;
      if (fuel <= 0) {
        _result = 1u;
      } else {
        unsigned int fuel_ = fuel - 1;
        if (n <= 0u) {
          _result = 1u;
        } else {
          if (n == 1u) {
            _result = 1u;
          } else {
            if (n == 2u) {
              _result = 1u;
            } else {
              _stack.emplace_back(_Call1{(((n - 2u) > n ? 0 : (n - 2u))), fuel_,
                                         (((n - 1u) > n ? 0 : (n - 1u))),
                                         fuel_});
              _stack.emplace_back(
                  _Enter{(((n - 3u) > n ? 0 : (n - 3u))), fuel_});
            }
          }
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      _stack.emplace_back(_Call2{_result, _f._s2, _f._s3});
      _stack.emplace_back(_Enter{_f._s0, _f._s1});
    } else if (std::holds_alternative<_Call2>(_frame)) {
      auto _f = std::move(std::get<_Call2>(_frame));
      _stack.emplace_back(_Call3{_f._s0, _result});
      _stack.emplace_back(_Enter{_f._s1, _f._s2});
    } else {
      auto _f = std::move(std::get<_Call3>(_frame));
      _result = ((_result * _f._s1) + _f._s0);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyMultiRecursion::mixed_arith(const unsigned int &n) {
  return mixed_arith_fuel((n * 3u), n);
}

__attribute__((pure)) bool
LoopifyMultiRecursion::bool_or_chain_fuel(const unsigned int &fuel,
                                          const unsigned int &n,
                                          const unsigned int &target) {
  struct _Enter {
    const unsigned int n;
    const unsigned int fuel;
  };

  struct _Call1 {
    decltype((((std::declval<const unsigned int &>() - 1u) >
                       std::declval<const unsigned int &>()
                   ? 0
                   : (std::declval<const unsigned int &>() - 1u)))) _s0;
    unsigned int _s1;
    decltype(std::declval<const unsigned int &>() ==
             std::declval<const unsigned int &>()) _s2;
  };

  struct _Call2 {
    bool _s0;
    decltype(std::declval<const unsigned int &>() ==
             std::declval<const unsigned int &>()) _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &n = _f.n;
      const unsigned int &fuel = _f.fuel;
      if (fuel <= 0) {
        _result = false;
      } else {
        unsigned int fuel_ = fuel - 1;
        if (n <= 0u) {
          _result = false;
        } else {
          _stack.emplace_back(
              _Call1{(((n - 1u) > n ? 0 : (n - 1u))), fuel_, n == target});
          _stack.emplace_back(_Enter{(((n - 2u) > n ? 0 : (n - 2u))), fuel_});
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      _stack.emplace_back(_Call2{_result, _f._s2});
      _stack.emplace_back(_Enter{_f._s0, _f._s1});
    } else {
      auto _f = std::move(std::get<_Call2>(_frame));
      _result = ((_f._s1 || _result) || _f._s0);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyMultiRecursion::bool_or_chain(const unsigned int &n,
                                     const unsigned int &target) {
  if (bool_or_chain_fuel((n * 2u), n, target)) {
    return 1u;
  } else {
    return 0u;
  }
}

__attribute__((pure)) bool
LoopifyMultiRecursion::bool_and_chain_fuel(const unsigned int &fuel,
                                           const unsigned int &n) {
  struct _Enter {
    const unsigned int n;
    const unsigned int fuel;
  };

  struct _Call1 {
    decltype((((std::declval<const unsigned int &>() - 1u) >
                       std::declval<const unsigned int &>()
                   ? 0
                   : (std::declval<const unsigned int &>() - 1u)))) _s0;
    unsigned int _s1;
  };

  struct _Call2 {
    bool _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &n = _f.n;
      const unsigned int &fuel = _f.fuel;
      if (fuel <= 0) {
        _result = true;
      } else {
        unsigned int fuel_ = fuel - 1;
        if (n <= 2u) {
          _result = true;
        } else {
          _stack.emplace_back(_Call1{(((n - 1u) > n ? 0 : (n - 1u))), fuel_});
          _stack.emplace_back(_Enter{(((n - 2u) > n ? 0 : (n - 2u))), fuel_});
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      _stack.emplace_back(_Call2{_result});
      _stack.emplace_back(_Enter{_f._s0, _f._s1});
    } else {
      auto _f = std::move(std::get<_Call2>(_frame));
      _result = (_result && _f._s0);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyMultiRecursion::bool_and_chain(const unsigned int &n) {
  if (bool_and_chain_fuel((n * 2u), n)) {
    return 1u;
  } else {
    return 0u;
  }
}

__attribute__((pure)) unsigned int LoopifyMultiRecursion::quad_count_leaves(
    const LoopifyMultiRecursion::quadtree &t) {
  struct _Enter {
    const LoopifyMultiRecursion::quadtree t;
  };

  struct _Call1 {
    const LoopifyMultiRecursion::quadtree _s0;
    const LoopifyMultiRecursion::quadtree _s1;
    const LoopifyMultiRecursion::quadtree _s2;
  };

  struct _Call2 {
    unsigned int _s0;
    const LoopifyMultiRecursion::quadtree _s1;
    const LoopifyMultiRecursion::quadtree _s2;
  };

  struct _Call3 {
    unsigned int _s0;
    unsigned int _s1;
    const LoopifyMultiRecursion::quadtree _s2;
  };

  struct _Call4 {
    unsigned int _s0;
    unsigned int _s1;
    unsigned int _s2;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyMultiRecursion::quadtree &t = _f.t;
      if (std::holds_alternative<
              typename LoopifyMultiRecursion::quadtree::QLeaf>(t.v())) {
        _result = 1u;
      } else {
        const auto &[d_a0, d_a1, d_a2, d_a3] =
            std::get<typename LoopifyMultiRecursion::quadtree::QQuad>(t.v());
        _stack.emplace_back(_Call1{*(d_a2), *(d_a1), *(d_a0)});
        _stack.emplace_back(_Enter{*(d_a3)});
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      _stack.emplace_back(_Call2{_result, _f._s1, _f._s2});
      _stack.emplace_back(_Enter{_f._s0});
    } else if (std::holds_alternative<_Call2>(_frame)) {
      auto _f = std::move(std::get<_Call2>(_frame));
      _stack.emplace_back(_Call3{_f._s0, _result, _f._s2});
      _stack.emplace_back(_Enter{_f._s1});
    } else if (std::holds_alternative<_Call3>(_frame)) {
      auto _f = std::move(std::get<_Call3>(_frame));
      _stack.emplace_back(_Call4{_f._s0, _f._s1, _result});
      _stack.emplace_back(_Enter{_f._s2});
    } else {
      auto _f = std::move(std::get<_Call4>(_frame));
      _result = (((_result + _f._s2) + _f._s1) + _f._s0);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyMultiRecursion::quad_depth(const LoopifyMultiRecursion::quadtree &t) {
  struct _Enter {
    const LoopifyMultiRecursion::quadtree t;
  };

  struct _Call1 {
    const LoopifyMultiRecursion::quadtree _s0;
    const LoopifyMultiRecursion::quadtree _s1;
    const LoopifyMultiRecursion::quadtree _s2;
    decltype(1u) _s3;
  };

  struct _Call2 {
    unsigned int _s0;
    const LoopifyMultiRecursion::quadtree _s1;
    const LoopifyMultiRecursion::quadtree _s2;
    decltype(1u) _s3;
  };

  struct _Call3 {
    unsigned int _s0;
    unsigned int _s1;
    const LoopifyMultiRecursion::quadtree _s2;
    decltype(1u) _s3;
  };

  struct _Call4 {
    unsigned int _s0;
    unsigned int _s1;
    unsigned int _s2;
    decltype(1u) _s3;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyMultiRecursion::quadtree &t = _f.t;
      if (std::holds_alternative<
              typename LoopifyMultiRecursion::quadtree::QLeaf>(t.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1, d_a2, d_a3] =
            std::get<typename LoopifyMultiRecursion::quadtree::QQuad>(t.v());
        _stack.emplace_back(_Call1{*(d_a2), *(d_a1), *(d_a0), 1u});
        _stack.emplace_back(_Enter{*(d_a3)});
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      _stack.emplace_back(_Call2{_result, _f._s1, _f._s2, _f._s3});
      _stack.emplace_back(_Enter{_f._s0});
    } else if (std::holds_alternative<_Call2>(_frame)) {
      auto _f = std::move(std::get<_Call2>(_frame));
      _stack.emplace_back(_Call3{_f._s0, _result, _f._s2, _f._s3});
      _stack.emplace_back(_Enter{_f._s1});
    } else if (std::holds_alternative<_Call3>(_frame)) {
      auto _f = std::move(std::get<_Call3>(_frame));
      _stack.emplace_back(_Call4{_f._s0, _f._s1, _result, _f._s3});
      _stack.emplace_back(_Enter{_f._s2});
    } else {
      auto _f = std::move(std::get<_Call4>(_frame));
      _result = (_f._s3 +
                 std::max(std::max(_result, _f._s2), std::max(_f._s1, _f._s0)));
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyMultiRecursion::hofstadter_q_fuel(const unsigned int &fuel,
                                         const unsigned int &n) {
  struct _Enter {
    const unsigned int n;
    const unsigned int fuel;
  };

  struct _Call1 {
    unsigned int _s0;
    const unsigned int _s1;
  };

  struct _Call2 {
    unsigned int _s0;
    const unsigned int _s1;
    unsigned int _s2;
  };

  struct _Call3 {
    decltype((
        ((std::declval<const unsigned int &>() -
          std::declval<unsigned int &>()) > std::declval<const unsigned int &>()
             ? 0
             : (std::declval<const unsigned int &>() -
                std::declval<unsigned int &>())))) _s0;
    unsigned int _s1;
  };

  struct _Call4 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &n = _f.n;
      const unsigned int &fuel = _f.fuel;
      if (fuel <= 0) {
        _result = 1u;
      } else {
        unsigned int fuel_ = fuel - 1;
        if (n <= 0u) {
          _result = 0u;
        } else {
          if (n == 1u) {
            _result = 1u;
          } else {
            if (n == 2u) {
              _result = 1u;
            } else {
              _stack.emplace_back(_Call1{fuel_, n});
              _stack.emplace_back(
                  _Enter{(((n - 1u) > n ? 0 : (n - 1u))), fuel_});
            }
          }
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int fuel_ = _f._s0;
      const unsigned int &n = _f._s1;
      unsigned int q1 = _result;
      _stack.emplace_back(_Call2{fuel_, n, q1});
      _stack.emplace_back(_Enter{(((n - 2u) > n ? 0 : (n - 2u))), fuel_});
    } else if (std::holds_alternative<_Call2>(_frame)) {
      auto _f = std::move(std::get<_Call2>(_frame));
      unsigned int fuel_ = _f._s0;
      const unsigned int &n = _f._s1;
      unsigned int q1 = _f._s2;
      unsigned int q2 = _result;
      _stack.emplace_back(_Call3{(((n - q1) > n ? 0 : (n - q1))), fuel_});
      _stack.emplace_back(_Enter{(((n - q2) > n ? 0 : (n - q2))), fuel_});
    } else if (std::holds_alternative<_Call3>(_frame)) {
      auto _f = std::move(std::get<_Call3>(_frame));
      _stack.emplace_back(_Call4{_result});
      _stack.emplace_back(_Enter{_f._s0, _f._s1});
    } else {
      auto _f = std::move(std::get<_Call4>(_frame));
      _result = (_result + _f._s0);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyMultiRecursion::hofstadter_q(const unsigned int &n) {
  return hofstadter_q_fuel(((n * n) + 1u), n);
}
