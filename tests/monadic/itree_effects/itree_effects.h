#ifndef INCLUDED_ITREE_EFFECTS
#define INCLUDED_ITREE_EFFECTS

#include <cstdlib>
#include <ctime>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

using namespace std::string_literals;
template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct Uint {
  // TYPES
  struct Nil {};

  struct D0 {
    std::unique_ptr<Uint> d_a0;
  };

  struct D1 {
    std::unique_ptr<Uint> d_a0;
  };

  struct D2 {
    std::unique_ptr<Uint> d_a0;
  };

  struct D3 {
    std::unique_ptr<Uint> d_a0;
  };

  struct D4 {
    std::unique_ptr<Uint> d_a0;
  };

  struct D5 {
    std::unique_ptr<Uint> d_a0;
  };

  struct D6 {
    std::unique_ptr<Uint> d_a0;
  };

  struct D7 {
    std::unique_ptr<Uint> d_a0;
  };

  struct D8 {
    std::unique_ptr<Uint> d_a0;
  };

  struct D9 {
    std::unique_ptr<Uint> d_a0;
  };

  using variant_t = std::variant<Nil, D0, D1, D2, D3, D4, D5, D6, D7, D8, D9>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Uint() {}

  explicit Uint(Nil _v) : d_v_(_v) {}

  explicit Uint(D0 _v) : d_v_(std::move(_v)) {}

  explicit Uint(D1 _v) : d_v_(std::move(_v)) {}

  explicit Uint(D2 _v) : d_v_(std::move(_v)) {}

  explicit Uint(D3 _v) : d_v_(std::move(_v)) {}

  explicit Uint(D4 _v) : d_v_(std::move(_v)) {}

  explicit Uint(D5 _v) : d_v_(std::move(_v)) {}

  explicit Uint(D6 _v) : d_v_(std::move(_v)) {}

  explicit Uint(D7 _v) : d_v_(std::move(_v)) {}

  explicit Uint(D8 _v) : d_v_(std::move(_v)) {}

  explicit Uint(D9 _v) : d_v_(std::move(_v)) {}

  Uint(const Uint &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Uint(Uint &&_other) : d_v_(std::move(_other.d_v_)) {}

  Uint &operator=(const Uint &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  Uint &operator=(Uint &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  Uint clone() const {
    Uint _out{};

    struct _CloneFrame {
      const Uint *_src;
      Uint *_dst;
    };

    std::vector<_CloneFrame> _stack;
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const Uint *_src = _frame._src;
      Uint *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        const auto &_alt = std::get<Nil>(_src->v());
        _dst->d_v_ = Nil{};
      } else if (std::holds_alternative<D0>(_src->v())) {
        const auto &_alt = std::get<D0>(_src->v());
        _dst->d_v_ = D0{_alt.d_a0 ? std::make_unique<Uint>() : nullptr};
        auto &_dst_alt = std::get<D0>(_dst->d_v_);
        if (_alt.d_a0)
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
      } else if (std::holds_alternative<D1>(_src->v())) {
        const auto &_alt = std::get<D1>(_src->v());
        _dst->d_v_ = D1{_alt.d_a0 ? std::make_unique<Uint>() : nullptr};
        auto &_dst_alt = std::get<D1>(_dst->d_v_);
        if (_alt.d_a0)
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
      } else if (std::holds_alternative<D2>(_src->v())) {
        const auto &_alt = std::get<D2>(_src->v());
        _dst->d_v_ = D2{_alt.d_a0 ? std::make_unique<Uint>() : nullptr};
        auto &_dst_alt = std::get<D2>(_dst->d_v_);
        if (_alt.d_a0)
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
      } else if (std::holds_alternative<D3>(_src->v())) {
        const auto &_alt = std::get<D3>(_src->v());
        _dst->d_v_ = D3{_alt.d_a0 ? std::make_unique<Uint>() : nullptr};
        auto &_dst_alt = std::get<D3>(_dst->d_v_);
        if (_alt.d_a0)
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
      } else if (std::holds_alternative<D4>(_src->v())) {
        const auto &_alt = std::get<D4>(_src->v());
        _dst->d_v_ = D4{_alt.d_a0 ? std::make_unique<Uint>() : nullptr};
        auto &_dst_alt = std::get<D4>(_dst->d_v_);
        if (_alt.d_a0)
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
      } else if (std::holds_alternative<D5>(_src->v())) {
        const auto &_alt = std::get<D5>(_src->v());
        _dst->d_v_ = D5{_alt.d_a0 ? std::make_unique<Uint>() : nullptr};
        auto &_dst_alt = std::get<D5>(_dst->d_v_);
        if (_alt.d_a0)
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
      } else if (std::holds_alternative<D6>(_src->v())) {
        const auto &_alt = std::get<D6>(_src->v());
        _dst->d_v_ = D6{_alt.d_a0 ? std::make_unique<Uint>() : nullptr};
        auto &_dst_alt = std::get<D6>(_dst->d_v_);
        if (_alt.d_a0)
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
      } else if (std::holds_alternative<D7>(_src->v())) {
        const auto &_alt = std::get<D7>(_src->v());
        _dst->d_v_ = D7{_alt.d_a0 ? std::make_unique<Uint>() : nullptr};
        auto &_dst_alt = std::get<D7>(_dst->d_v_);
        if (_alt.d_a0)
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
      } else if (std::holds_alternative<D8>(_src->v())) {
        const auto &_alt = std::get<D8>(_src->v());
        _dst->d_v_ = D8{_alt.d_a0 ? std::make_unique<Uint>() : nullptr};
        auto &_dst_alt = std::get<D8>(_dst->d_v_);
        if (_alt.d_a0)
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
      } else {
        const auto &_alt = std::get<D9>(_src->v());
        _dst->d_v_ = D9{_alt.d_a0 ? std::make_unique<Uint>() : nullptr};
        auto &_dst_alt = std::get<D9>(_dst->d_v_);
        if (_alt.d_a0)
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
      }
    }
    return _out;
  }

  // CREATORS
  static Uint nil() { return Uint(Nil{}); }

  static Uint d0(Uint a0) {
    return Uint(D0{std::make_unique<Uint>(std::move(a0))});
  }

  static Uint d1(Uint a0) {
    return Uint(D1{std::make_unique<Uint>(std::move(a0))});
  }

  static Uint d2(Uint a0) {
    return Uint(D2{std::make_unique<Uint>(std::move(a0))});
  }

  static Uint d3(Uint a0) {
    return Uint(D3{std::make_unique<Uint>(std::move(a0))});
  }

  static Uint d4(Uint a0) {
    return Uint(D4{std::make_unique<Uint>(std::move(a0))});
  }

  static Uint d5(Uint a0) {
    return Uint(D5{std::make_unique<Uint>(std::move(a0))});
  }

  static Uint d6(Uint a0) {
    return Uint(D6{std::make_unique<Uint>(std::move(a0))});
  }

  static Uint d7(Uint a0) {
    return Uint(D7{std::make_unique<Uint>(std::move(a0))});
  }

  static Uint d8(Uint a0) {
    return Uint(D8{std::make_unique<Uint>(std::move(a0))});
  }

  static Uint d9(Uint a0) {
    return Uint(D9{std::make_unique<Uint>(std::move(a0))});
  }

  // MANIPULATORS
  ~Uint() {
    std::vector<std::unique_ptr<Uint>> _stack;
    auto _drain = [&](Uint &_node) {
      if (std::holds_alternative<D0>(_node.d_v_)) {
        auto &_alt = std::get<D0>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<D1>(_node.d_v_)) {
        auto &_alt = std::get<D1>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<D2>(_node.d_v_)) {
        auto &_alt = std::get<D2>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<D3>(_node.d_v_)) {
        auto &_alt = std::get<D3>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<D4>(_node.d_v_)) {
        auto &_alt = std::get<D4>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<D5>(_node.d_v_)) {
        auto &_alt = std::get<D5>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<D6>(_node.d_v_)) {
        auto &_alt = std::get<D6>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<D7>(_node.d_v_)) {
        auto &_alt = std::get<D7>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<D8>(_node.d_v_)) {
        auto &_alt = std::get<D8>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<D9>(_node.d_v_)) {
        auto &_alt = std::get<D9>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node)
        _drain(*_node);
    }
  }

  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }
};

struct Uint0 {
  // TYPES
  struct Nil0 {};

  struct D10 {
    std::unique_ptr<Uint0> d_a0;
  };

  struct D11 {
    std::unique_ptr<Uint0> d_a0;
  };

  struct D12 {
    std::unique_ptr<Uint0> d_a0;
  };

  struct D13 {
    std::unique_ptr<Uint0> d_a0;
  };

  struct D14 {
    std::unique_ptr<Uint0> d_a0;
  };

  struct D15 {
    std::unique_ptr<Uint0> d_a0;
  };

  struct D16 {
    std::unique_ptr<Uint0> d_a0;
  };

  struct D17 {
    std::unique_ptr<Uint0> d_a0;
  };

  struct D18 {
    std::unique_ptr<Uint0> d_a0;
  };

  struct D19 {
    std::unique_ptr<Uint0> d_a0;
  };

  struct Da {
    std::unique_ptr<Uint0> d_a0;
  };

  struct Db {
    std::unique_ptr<Uint0> d_a0;
  };

  struct Dc {
    std::unique_ptr<Uint0> d_a0;
  };

  struct Dd {
    std::unique_ptr<Uint0> d_a0;
  };

  struct De {
    std::unique_ptr<Uint0> d_a0;
  };

  struct Df {
    std::unique_ptr<Uint0> d_a0;
  };

  using variant_t = std::variant<Nil0, D10, D11, D12, D13, D14, D15, D16, D17,
                                 D18, D19, Da, Db, Dc, Dd, De, Df>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Uint0() {}

  explicit Uint0(Nil0 _v) : d_v_(_v) {}

  explicit Uint0(D10 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(D11 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(D12 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(D13 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(D14 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(D15 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(D16 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(D17 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(D18 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(D19 _v) : d_v_(std::move(_v)) {}

  explicit Uint0(Da _v) : d_v_(std::move(_v)) {}

  explicit Uint0(Db _v) : d_v_(std::move(_v)) {}

  explicit Uint0(Dc _v) : d_v_(std::move(_v)) {}

  explicit Uint0(Dd _v) : d_v_(std::move(_v)) {}

  explicit Uint0(De _v) : d_v_(std::move(_v)) {}

  explicit Uint0(Df _v) : d_v_(std::move(_v)) {}

  Uint0(const Uint0 &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Uint0(Uint0 &&_other) : d_v_(std::move(_other.d_v_)) {}

  Uint0 &operator=(const Uint0 &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  Uint0 &operator=(Uint0 &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  Uint0 clone() const {
    Uint0 _out{};

    struct _CloneFrame {
      const Uint0 *_src;
      Uint0 *_dst;
    };

    std::vector<_CloneFrame> _stack;
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const Uint0 *_src = _frame._src;
      Uint0 *_dst = _frame._dst;
      if (std::holds_alternative<Nil0>(_src->v())) {
        const auto &_alt = std::get<Nil0>(_src->v());
        _dst->d_v_ = Nil0{};
      } else if (std::holds_alternative<D10>(_src->v())) {
        const auto &_alt = std::get<D10>(_src->v());
        _dst->d_v_ = D10{_alt.d_a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D10>(_dst->d_v_);
        if (_alt.d_a0)
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
      } else if (std::holds_alternative<D11>(_src->v())) {
        const auto &_alt = std::get<D11>(_src->v());
        _dst->d_v_ = D11{_alt.d_a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D11>(_dst->d_v_);
        if (_alt.d_a0)
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
      } else if (std::holds_alternative<D12>(_src->v())) {
        const auto &_alt = std::get<D12>(_src->v());
        _dst->d_v_ = D12{_alt.d_a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D12>(_dst->d_v_);
        if (_alt.d_a0)
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
      } else if (std::holds_alternative<D13>(_src->v())) {
        const auto &_alt = std::get<D13>(_src->v());
        _dst->d_v_ = D13{_alt.d_a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D13>(_dst->d_v_);
        if (_alt.d_a0)
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
      } else if (std::holds_alternative<D14>(_src->v())) {
        const auto &_alt = std::get<D14>(_src->v());
        _dst->d_v_ = D14{_alt.d_a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D14>(_dst->d_v_);
        if (_alt.d_a0)
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
      } else if (std::holds_alternative<D15>(_src->v())) {
        const auto &_alt = std::get<D15>(_src->v());
        _dst->d_v_ = D15{_alt.d_a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D15>(_dst->d_v_);
        if (_alt.d_a0)
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
      } else if (std::holds_alternative<D16>(_src->v())) {
        const auto &_alt = std::get<D16>(_src->v());
        _dst->d_v_ = D16{_alt.d_a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D16>(_dst->d_v_);
        if (_alt.d_a0)
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
      } else if (std::holds_alternative<D17>(_src->v())) {
        const auto &_alt = std::get<D17>(_src->v());
        _dst->d_v_ = D17{_alt.d_a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D17>(_dst->d_v_);
        if (_alt.d_a0)
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
      } else if (std::holds_alternative<D18>(_src->v())) {
        const auto &_alt = std::get<D18>(_src->v());
        _dst->d_v_ = D18{_alt.d_a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D18>(_dst->d_v_);
        if (_alt.d_a0)
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
      } else if (std::holds_alternative<D19>(_src->v())) {
        const auto &_alt = std::get<D19>(_src->v());
        _dst->d_v_ = D19{_alt.d_a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D19>(_dst->d_v_);
        if (_alt.d_a0)
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
      } else if (std::holds_alternative<Da>(_src->v())) {
        const auto &_alt = std::get<Da>(_src->v());
        _dst->d_v_ = Da{_alt.d_a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<Da>(_dst->d_v_);
        if (_alt.d_a0)
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
      } else if (std::holds_alternative<Db>(_src->v())) {
        const auto &_alt = std::get<Db>(_src->v());
        _dst->d_v_ = Db{_alt.d_a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<Db>(_dst->d_v_);
        if (_alt.d_a0)
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
      } else if (std::holds_alternative<Dc>(_src->v())) {
        const auto &_alt = std::get<Dc>(_src->v());
        _dst->d_v_ = Dc{_alt.d_a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<Dc>(_dst->d_v_);
        if (_alt.d_a0)
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
      } else if (std::holds_alternative<Dd>(_src->v())) {
        const auto &_alt = std::get<Dd>(_src->v());
        _dst->d_v_ = Dd{_alt.d_a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<Dd>(_dst->d_v_);
        if (_alt.d_a0)
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
      } else if (std::holds_alternative<De>(_src->v())) {
        const auto &_alt = std::get<De>(_src->v());
        _dst->d_v_ = De{_alt.d_a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<De>(_dst->d_v_);
        if (_alt.d_a0)
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
      } else {
        const auto &_alt = std::get<Df>(_src->v());
        _dst->d_v_ = Df{_alt.d_a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<Df>(_dst->d_v_);
        if (_alt.d_a0)
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
      }
    }
    return _out;
  }

  // CREATORS
  static Uint0 nil0() { return Uint0(Nil0{}); }

  static Uint0 d10(Uint0 a0) {
    return Uint0(D10{std::make_unique<Uint0>(std::move(a0))});
  }

  static Uint0 d11(Uint0 a0) {
    return Uint0(D11{std::make_unique<Uint0>(std::move(a0))});
  }

  static Uint0 d12(Uint0 a0) {
    return Uint0(D12{std::make_unique<Uint0>(std::move(a0))});
  }

  static Uint0 d13(Uint0 a0) {
    return Uint0(D13{std::make_unique<Uint0>(std::move(a0))});
  }

  static Uint0 d14(Uint0 a0) {
    return Uint0(D14{std::make_unique<Uint0>(std::move(a0))});
  }

  static Uint0 d15(Uint0 a0) {
    return Uint0(D15{std::make_unique<Uint0>(std::move(a0))});
  }

  static Uint0 d16(Uint0 a0) {
    return Uint0(D16{std::make_unique<Uint0>(std::move(a0))});
  }

  static Uint0 d17(Uint0 a0) {
    return Uint0(D17{std::make_unique<Uint0>(std::move(a0))});
  }

  static Uint0 d18(Uint0 a0) {
    return Uint0(D18{std::make_unique<Uint0>(std::move(a0))});
  }

  static Uint0 d19(Uint0 a0) {
    return Uint0(D19{std::make_unique<Uint0>(std::move(a0))});
  }

  static Uint0 da(Uint0 a0) {
    return Uint0(Da{std::make_unique<Uint0>(std::move(a0))});
  }

  static Uint0 db(Uint0 a0) {
    return Uint0(Db{std::make_unique<Uint0>(std::move(a0))});
  }

  static Uint0 dc(Uint0 a0) {
    return Uint0(Dc{std::make_unique<Uint0>(std::move(a0))});
  }

  static Uint0 dd(Uint0 a0) {
    return Uint0(Dd{std::make_unique<Uint0>(std::move(a0))});
  }

  static Uint0 de(Uint0 a0) {
    return Uint0(De{std::make_unique<Uint0>(std::move(a0))});
  }

  static Uint0 df(Uint0 a0) {
    return Uint0(Df{std::make_unique<Uint0>(std::move(a0))});
  }

  // MANIPULATORS
  ~Uint0() {
    std::vector<std::unique_ptr<Uint0>> _stack;
    auto _drain = [&](Uint0 &_node) {
      if (std::holds_alternative<D10>(_node.d_v_)) {
        auto &_alt = std::get<D10>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<D11>(_node.d_v_)) {
        auto &_alt = std::get<D11>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<D12>(_node.d_v_)) {
        auto &_alt = std::get<D12>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<D13>(_node.d_v_)) {
        auto &_alt = std::get<D13>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<D14>(_node.d_v_)) {
        auto &_alt = std::get<D14>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<D15>(_node.d_v_)) {
        auto &_alt = std::get<D15>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<D16>(_node.d_v_)) {
        auto &_alt = std::get<D16>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<D17>(_node.d_v_)) {
        auto &_alt = std::get<D17>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<D18>(_node.d_v_)) {
        auto &_alt = std::get<D18>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<D19>(_node.d_v_)) {
        auto &_alt = std::get<D19>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<Da>(_node.d_v_)) {
        auto &_alt = std::get<Da>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<Db>(_node.d_v_)) {
        auto &_alt = std::get<Db>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<Dc>(_node.d_v_)) {
        auto &_alt = std::get<Dc>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<Dd>(_node.d_v_)) {
        auto &_alt = std::get<Dd>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<De>(_node.d_v_)) {
        auto &_alt = std::get<De>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
      if (std::holds_alternative<Df>(_node.d_v_)) {
        auto &_alt = std::get<Df>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node)
        _drain(*_node);
    }
  }

  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }
};

struct Uint1 {
  // TYPES
  struct UIntDecimal {
    Uint d_u;
  };

  struct UIntHexadecimal {
    Uint0 d_u;
  };

  using variant_t = std::variant<UIntDecimal, UIntHexadecimal>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Uint1() {}

  explicit Uint1(UIntDecimal _v) : d_v_(std::move(_v)) {}

  explicit Uint1(UIntHexadecimal _v) : d_v_(std::move(_v)) {}

  Uint1(const Uint1 &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Uint1(Uint1 &&_other) : d_v_(std::move(_other.d_v_)) {}

  Uint1 &operator=(const Uint1 &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  Uint1 &operator=(Uint1 &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  Uint1 clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<UIntDecimal>(_sv.v())) {
      const auto &[d_u] = std::get<UIntDecimal>(_sv.v());
      return Uint1(UIntDecimal{d_u.clone()});
    } else {
      const auto &[d_u] = std::get<UIntHexadecimal>(_sv.v());
      return Uint1(UIntHexadecimal{d_u.clone()});
    }
  }

  // CREATORS
  static Uint1 uintdecimal(Uint u) { return Uint1(UIntDecimal{std::move(u)}); }

  static Uint1 uinthexadecimal(Uint0 u) {
    return Uint1(UIntHexadecimal{std::move(u)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }
};

struct Nat {
  static unsigned int tail_add(const unsigned int &n, unsigned int m);
  static unsigned int tail_addmul(unsigned int r, const unsigned int &n,
                                  const unsigned int &m);
  static unsigned int tail_mul(const unsigned int &n, const unsigned int &m);
  static unsigned int of_uint_acc(const Uint &d, unsigned int acc);
  static unsigned int of_uint(const Uint &d);
  static unsigned int of_hex_uint_acc(const Uint0 &d, unsigned int acc);
  static unsigned int of_hex_uint(const Uint0 &d);
  static unsigned int of_num_uint(const Uint1 &d);
};

/// ------------------------------------------------------------------
struct ITreeEffects {
  static void greet();
  static unsigned int roll_dice(const unsigned int &sides);
  static void timed_greeting();
  static void echo_loop(const unsigned int &n);
};

#endif // INCLUDED_ITREE_EFFECTS
