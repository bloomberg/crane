#ifndef INCLUDED_HOF_TREE_LOOPIFY
#define INCLUDED_HOF_TREE_LOOPIFY

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct Uint {
  // TYPES
  struct Nil {};

  struct D0 {
    std::unique_ptr<Uint> a0;
  };

  struct D1 {
    std::unique_ptr<Uint> a0;
  };

  struct D2 {
    std::unique_ptr<Uint> a0;
  };

  struct D3 {
    std::unique_ptr<Uint> a0;
  };

  struct D4 {
    std::unique_ptr<Uint> a0;
  };

  struct D5 {
    std::unique_ptr<Uint> a0;
  };

  struct D6 {
    std::unique_ptr<Uint> a0;
  };

  struct D7 {
    std::unique_ptr<Uint> a0;
  };

  struct D8 {
    std::unique_ptr<Uint> a0;
  };

  struct D9 {
    std::unique_ptr<Uint> a0;
  };

  using variant_t = std::variant<Nil, D0, D1, D2, D3, D4, D5, D6, D7, D8, D9>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Uint() {}

  explicit Uint(Nil _v) : v_(_v) {}

  explicit Uint(D0 _v) : v_(std::move(_v)) {}

  explicit Uint(D1 _v) : v_(std::move(_v)) {}

  explicit Uint(D2 _v) : v_(std::move(_v)) {}

  explicit Uint(D3 _v) : v_(std::move(_v)) {}

  explicit Uint(D4 _v) : v_(std::move(_v)) {}

  explicit Uint(D5 _v) : v_(std::move(_v)) {}

  explicit Uint(D6 _v) : v_(std::move(_v)) {}

  explicit Uint(D7 _v) : v_(std::move(_v)) {}

  explicit Uint(D8 _v) : v_(std::move(_v)) {}

  explicit Uint(D9 _v) : v_(std::move(_v)) {}

  Uint(const Uint &_other) : v_(std::move(_other.clone().v_)) {}

  Uint(Uint &&_other) noexcept : v_(std::move(_other.v_)) {}

  Uint &operator=(const Uint &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  Uint &operator=(Uint &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  Uint clone() const {
    Uint _out{};

    struct _CloneFrame {
      const Uint *_src;
      Uint *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const Uint *_src = _frame._src;
      Uint *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->v_ = Nil{};
      } else if (std::holds_alternative<D0>(_src->v())) {
        const auto &_alt = std::get<D0>(_src->v());
        _dst->v_ = D0{_alt.a0 ? std::make_unique<Uint>() : nullptr};
        auto &_dst_alt = std::get<D0>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<D1>(_src->v())) {
        const auto &_alt = std::get<D1>(_src->v());
        _dst->v_ = D1{_alt.a0 ? std::make_unique<Uint>() : nullptr};
        auto &_dst_alt = std::get<D1>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<D2>(_src->v())) {
        const auto &_alt = std::get<D2>(_src->v());
        _dst->v_ = D2{_alt.a0 ? std::make_unique<Uint>() : nullptr};
        auto &_dst_alt = std::get<D2>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<D3>(_src->v())) {
        const auto &_alt = std::get<D3>(_src->v());
        _dst->v_ = D3{_alt.a0 ? std::make_unique<Uint>() : nullptr};
        auto &_dst_alt = std::get<D3>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<D4>(_src->v())) {
        const auto &_alt = std::get<D4>(_src->v());
        _dst->v_ = D4{_alt.a0 ? std::make_unique<Uint>() : nullptr};
        auto &_dst_alt = std::get<D4>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<D5>(_src->v())) {
        const auto &_alt = std::get<D5>(_src->v());
        _dst->v_ = D5{_alt.a0 ? std::make_unique<Uint>() : nullptr};
        auto &_dst_alt = std::get<D5>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<D6>(_src->v())) {
        const auto &_alt = std::get<D6>(_src->v());
        _dst->v_ = D6{_alt.a0 ? std::make_unique<Uint>() : nullptr};
        auto &_dst_alt = std::get<D6>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<D7>(_src->v())) {
        const auto &_alt = std::get<D7>(_src->v());
        _dst->v_ = D7{_alt.a0 ? std::make_unique<Uint>() : nullptr};
        auto &_dst_alt = std::get<D7>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<D8>(_src->v())) {
        const auto &_alt = std::get<D8>(_src->v());
        _dst->v_ = D8{_alt.a0 ? std::make_unique<Uint>() : nullptr};
        auto &_dst_alt = std::get<D8>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else {
        const auto &_alt = std::get<D9>(_src->v());
        _dst->v_ = D9{_alt.a0 ? std::make_unique<Uint>() : nullptr};
        auto &_dst_alt = std::get<D9>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
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
    std::vector<std::unique_ptr<Uint>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](Uint &_node) {
      if (std::holds_alternative<D0>(_node.v_)) {
        auto &_alt = std::get<D0>(_node.v_);
        if (_alt.a0) {
          _stack.push_back(std::move(_alt.a0));
        }
      }
      if (std::holds_alternative<D1>(_node.v_)) {
        auto &_alt = std::get<D1>(_node.v_);
        if (_alt.a0) {
          _stack.push_back(std::move(_alt.a0));
        }
      }
      if (std::holds_alternative<D2>(_node.v_)) {
        auto &_alt = std::get<D2>(_node.v_);
        if (_alt.a0) {
          _stack.push_back(std::move(_alt.a0));
        }
      }
      if (std::holds_alternative<D3>(_node.v_)) {
        auto &_alt = std::get<D3>(_node.v_);
        if (_alt.a0) {
          _stack.push_back(std::move(_alt.a0));
        }
      }
      if (std::holds_alternative<D4>(_node.v_)) {
        auto &_alt = std::get<D4>(_node.v_);
        if (_alt.a0) {
          _stack.push_back(std::move(_alt.a0));
        }
      }
      if (std::holds_alternative<D5>(_node.v_)) {
        auto &_alt = std::get<D5>(_node.v_);
        if (_alt.a0) {
          _stack.push_back(std::move(_alt.a0));
        }
      }
      if (std::holds_alternative<D6>(_node.v_)) {
        auto &_alt = std::get<D6>(_node.v_);
        if (_alt.a0) {
          _stack.push_back(std::move(_alt.a0));
        }
      }
      if (std::holds_alternative<D7>(_node.v_)) {
        auto &_alt = std::get<D7>(_node.v_);
        if (_alt.a0) {
          _stack.push_back(std::move(_alt.a0));
        }
      }
      if (std::holds_alternative<D8>(_node.v_)) {
        auto &_alt = std::get<D8>(_node.v_);
        if (_alt.a0) {
          _stack.push_back(std::move(_alt.a0));
        }
      }
      if (std::holds_alternative<D9>(_node.v_)) {
        auto &_alt = std::get<D9>(_node.v_);
        if (_alt.a0) {
          _stack.push_back(std::move(_alt.a0));
        }
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node) {
        _drain(*_node);
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Uint0 {
  // TYPES
  struct Nil0 {};

  struct D10 {
    std::unique_ptr<Uint0> a0;
  };

  struct D11 {
    std::unique_ptr<Uint0> a0;
  };

  struct D12 {
    std::unique_ptr<Uint0> a0;
  };

  struct D13 {
    std::unique_ptr<Uint0> a0;
  };

  struct D14 {
    std::unique_ptr<Uint0> a0;
  };

  struct D15 {
    std::unique_ptr<Uint0> a0;
  };

  struct D16 {
    std::unique_ptr<Uint0> a0;
  };

  struct D17 {
    std::unique_ptr<Uint0> a0;
  };

  struct D18 {
    std::unique_ptr<Uint0> a0;
  };

  struct D19 {
    std::unique_ptr<Uint0> a0;
  };

  struct Da {
    std::unique_ptr<Uint0> a0;
  };

  struct Db {
    std::unique_ptr<Uint0> a0;
  };

  struct Dc {
    std::unique_ptr<Uint0> a0;
  };

  struct Dd {
    std::unique_ptr<Uint0> a0;
  };

  struct De {
    std::unique_ptr<Uint0> a0;
  };

  struct Df {
    std::unique_ptr<Uint0> a0;
  };

  using variant_t = std::variant<Nil0, D10, D11, D12, D13, D14, D15, D16, D17,
                                 D18, D19, Da, Db, Dc, Dd, De, Df>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Uint0() {}

  explicit Uint0(Nil0 _v) : v_(_v) {}

  explicit Uint0(D10 _v) : v_(std::move(_v)) {}

  explicit Uint0(D11 _v) : v_(std::move(_v)) {}

  explicit Uint0(D12 _v) : v_(std::move(_v)) {}

  explicit Uint0(D13 _v) : v_(std::move(_v)) {}

  explicit Uint0(D14 _v) : v_(std::move(_v)) {}

  explicit Uint0(D15 _v) : v_(std::move(_v)) {}

  explicit Uint0(D16 _v) : v_(std::move(_v)) {}

  explicit Uint0(D17 _v) : v_(std::move(_v)) {}

  explicit Uint0(D18 _v) : v_(std::move(_v)) {}

  explicit Uint0(D19 _v) : v_(std::move(_v)) {}

  explicit Uint0(Da _v) : v_(std::move(_v)) {}

  explicit Uint0(Db _v) : v_(std::move(_v)) {}

  explicit Uint0(Dc _v) : v_(std::move(_v)) {}

  explicit Uint0(Dd _v) : v_(std::move(_v)) {}

  explicit Uint0(De _v) : v_(std::move(_v)) {}

  explicit Uint0(Df _v) : v_(std::move(_v)) {}

  Uint0(const Uint0 &_other) : v_(std::move(_other.clone().v_)) {}

  Uint0(Uint0 &&_other) noexcept : v_(std::move(_other.v_)) {}

  Uint0 &operator=(const Uint0 &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  Uint0 &operator=(Uint0 &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  Uint0 clone() const {
    Uint0 _out{};

    struct _CloneFrame {
      const Uint0 *_src;
      Uint0 *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const Uint0 *_src = _frame._src;
      Uint0 *_dst = _frame._dst;
      if (std::holds_alternative<Nil0>(_src->v())) {
        _dst->v_ = Nil0{};
      } else if (std::holds_alternative<D10>(_src->v())) {
        const auto &_alt = std::get<D10>(_src->v());
        _dst->v_ = D10{_alt.a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D10>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<D11>(_src->v())) {
        const auto &_alt = std::get<D11>(_src->v());
        _dst->v_ = D11{_alt.a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D11>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<D12>(_src->v())) {
        const auto &_alt = std::get<D12>(_src->v());
        _dst->v_ = D12{_alt.a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D12>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<D13>(_src->v())) {
        const auto &_alt = std::get<D13>(_src->v());
        _dst->v_ = D13{_alt.a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D13>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<D14>(_src->v())) {
        const auto &_alt = std::get<D14>(_src->v());
        _dst->v_ = D14{_alt.a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D14>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<D15>(_src->v())) {
        const auto &_alt = std::get<D15>(_src->v());
        _dst->v_ = D15{_alt.a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D15>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<D16>(_src->v())) {
        const auto &_alt = std::get<D16>(_src->v());
        _dst->v_ = D16{_alt.a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D16>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<D17>(_src->v())) {
        const auto &_alt = std::get<D17>(_src->v());
        _dst->v_ = D17{_alt.a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D17>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<D18>(_src->v())) {
        const auto &_alt = std::get<D18>(_src->v());
        _dst->v_ = D18{_alt.a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D18>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<D19>(_src->v())) {
        const auto &_alt = std::get<D19>(_src->v());
        _dst->v_ = D19{_alt.a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D19>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<Da>(_src->v())) {
        const auto &_alt = std::get<Da>(_src->v());
        _dst->v_ = Da{_alt.a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<Da>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<Db>(_src->v())) {
        const auto &_alt = std::get<Db>(_src->v());
        _dst->v_ = Db{_alt.a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<Db>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<Dc>(_src->v())) {
        const auto &_alt = std::get<Dc>(_src->v());
        _dst->v_ = Dc{_alt.a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<Dc>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<Dd>(_src->v())) {
        const auto &_alt = std::get<Dd>(_src->v());
        _dst->v_ = Dd{_alt.a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<Dd>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<De>(_src->v())) {
        const auto &_alt = std::get<De>(_src->v());
        _dst->v_ = De{_alt.a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<De>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else {
        const auto &_alt = std::get<Df>(_src->v());
        _dst->v_ = Df{_alt.a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<Df>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
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
    std::vector<std::unique_ptr<Uint0>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](Uint0 &_node) {
      if (std::holds_alternative<D10>(_node.v_)) {
        auto &_alt = std::get<D10>(_node.v_);
        if (_alt.a0) {
          _stack.push_back(std::move(_alt.a0));
        }
      }
      if (std::holds_alternative<D11>(_node.v_)) {
        auto &_alt = std::get<D11>(_node.v_);
        if (_alt.a0) {
          _stack.push_back(std::move(_alt.a0));
        }
      }
      if (std::holds_alternative<D12>(_node.v_)) {
        auto &_alt = std::get<D12>(_node.v_);
        if (_alt.a0) {
          _stack.push_back(std::move(_alt.a0));
        }
      }
      if (std::holds_alternative<D13>(_node.v_)) {
        auto &_alt = std::get<D13>(_node.v_);
        if (_alt.a0) {
          _stack.push_back(std::move(_alt.a0));
        }
      }
      if (std::holds_alternative<D14>(_node.v_)) {
        auto &_alt = std::get<D14>(_node.v_);
        if (_alt.a0) {
          _stack.push_back(std::move(_alt.a0));
        }
      }
      if (std::holds_alternative<D15>(_node.v_)) {
        auto &_alt = std::get<D15>(_node.v_);
        if (_alt.a0) {
          _stack.push_back(std::move(_alt.a0));
        }
      }
      if (std::holds_alternative<D16>(_node.v_)) {
        auto &_alt = std::get<D16>(_node.v_);
        if (_alt.a0) {
          _stack.push_back(std::move(_alt.a0));
        }
      }
      if (std::holds_alternative<D17>(_node.v_)) {
        auto &_alt = std::get<D17>(_node.v_);
        if (_alt.a0) {
          _stack.push_back(std::move(_alt.a0));
        }
      }
      if (std::holds_alternative<D18>(_node.v_)) {
        auto &_alt = std::get<D18>(_node.v_);
        if (_alt.a0) {
          _stack.push_back(std::move(_alt.a0));
        }
      }
      if (std::holds_alternative<D19>(_node.v_)) {
        auto &_alt = std::get<D19>(_node.v_);
        if (_alt.a0) {
          _stack.push_back(std::move(_alt.a0));
        }
      }
      if (std::holds_alternative<Da>(_node.v_)) {
        auto &_alt = std::get<Da>(_node.v_);
        if (_alt.a0) {
          _stack.push_back(std::move(_alt.a0));
        }
      }
      if (std::holds_alternative<Db>(_node.v_)) {
        auto &_alt = std::get<Db>(_node.v_);
        if (_alt.a0) {
          _stack.push_back(std::move(_alt.a0));
        }
      }
      if (std::holds_alternative<Dc>(_node.v_)) {
        auto &_alt = std::get<Dc>(_node.v_);
        if (_alt.a0) {
          _stack.push_back(std::move(_alt.a0));
        }
      }
      if (std::holds_alternative<Dd>(_node.v_)) {
        auto &_alt = std::get<Dd>(_node.v_);
        if (_alt.a0) {
          _stack.push_back(std::move(_alt.a0));
        }
      }
      if (std::holds_alternative<De>(_node.v_)) {
        auto &_alt = std::get<De>(_node.v_);
        if (_alt.a0) {
          _stack.push_back(std::move(_alt.a0));
        }
      }
      if (std::holds_alternative<Df>(_node.v_)) {
        auto &_alt = std::get<Df>(_node.v_);
        if (_alt.a0) {
          _stack.push_back(std::move(_alt.a0));
        }
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node) {
        _drain(*_node);
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Uint1 {
  // TYPES
  struct UIntDecimal {
    Uint u;
  };

  struct UIntHexadecimal {
    Uint0 u;
  };

  using variant_t = std::variant<UIntDecimal, UIntHexadecimal>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Uint1() {}

  explicit Uint1(UIntDecimal _v) : v_(std::move(_v)) {}

  explicit Uint1(UIntHexadecimal _v) : v_(std::move(_v)) {}

  Uint1(const Uint1 &_other) : v_(std::move(_other.clone().v_)) {}

  Uint1(Uint1 &&_other) noexcept : v_(std::move(_other.v_)) {}

  Uint1 &operator=(const Uint1 &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  Uint1 &operator=(Uint1 &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  Uint1 clone() const {
    if (std::holds_alternative<UIntDecimal>(this->v())) {
      const auto &[u] = std::get<UIntDecimal>(this->v());
      return Uint1(UIntDecimal{u.clone()});
    } else {
      const auto &[u] = std::get<UIntHexadecimal>(this->v());
      return Uint1(UIntHexadecimal{u.clone()});
    }
  }

  // CREATORS
  static Uint1 uintdecimal(Uint u) { return Uint1(UIntDecimal{std::move(u)}); }

  static Uint1 uinthexadecimal(Uint0 u) {
    return Uint1(UIntHexadecimal{std::move(u)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Nat {
  static uint64_t tail_add(uint64_t n, uint64_t m);
  static uint64_t tail_addmul(uint64_t r, uint64_t n, uint64_t m);
  static uint64_t tail_mul(uint64_t n, uint64_t m);
  static uint64_t of_uint_acc(const Uint &d, uint64_t acc);
  static uint64_t of_uint(const Uint &d);
  static uint64_t of_hex_uint_acc(const Uint0 &d, uint64_t acc);
  static uint64_t of_hex_uint(const Uint0 &d);
  static uint64_t of_num_uint(const Uint1 &d);
};

struct HofTreeLoopify {
  template <typename A> struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::unique_ptr<tree<A>> l;
      A x;
      std::unique_ptr<tree<A>> r;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Leaf _v) : v_(_v) {}

    explicit tree(Node _v) : v_(std::move(_v)) {}

    tree(const tree<A> &_other) : v_(std::move(_other.clone().v_)) {}

    tree(tree<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

    tree<A> &operator=(const tree<A> &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    tree<A> &operator=(tree<A> &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    tree<A> clone() const {
      tree<A> _out{};

      struct _CloneFrame {
        const tree<A> *_src;
        tree<A> *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const tree<A> *_src = _frame._src;
        tree<A> *_dst = _frame._dst;
        if (std::holds_alternative<Leaf>(_src->v())) {
          _dst->v_ = Leaf{};
        } else {
          const auto &_alt = std::get<Node>(_src->v());
          _dst->v_ =
              Node{_alt.l ? std::make_unique<tree<A>>() : nullptr, _alt.x,
                   _alt.r ? std::make_unique<tree<A>>() : nullptr};
          auto &_dst_alt = std::get<Node>(_dst->v_);
          if (_alt.l) {
            _stack.push_back({_alt.l.get(), _dst_alt.l.get()});
          }
          if (_alt.r) {
            _stack.push_back({_alt.r.get(), _dst_alt.r.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    template <typename _U> explicit tree(const tree<_U> &_other) {
      if (std::holds_alternative<typename tree<_U>::Leaf>(_other.v())) {
        this->v_ = Leaf{};
      } else {
        const auto &[l, x, r] = std::get<typename tree<_U>::Node>(_other.v());
        this->v_ = Node{l ? std::make_unique<tree<A>>(*l) : nullptr, A(x),
                        r ? std::make_unique<tree<A>>(*r) : nullptr};
      }
    }

    static tree<A> leaf() { return tree(Leaf{}); }

    static tree<A> node(tree<A> l, A x, tree<A> r) {
      return tree(Node{std::make_unique<tree<A>>(std::move(l)), std::move(x),
                       std::make_unique<tree<A>>(std::move(r))});
    }

    // MANIPULATORS
    ~tree() {
      std::vector<std::unique_ptr<tree<A>>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](tree<A> &_node) {
        if (std::holds_alternative<Node>(_node.v_)) {
          auto &_alt = std::get<Node>(_node.v_);
          if (_alt.l) {
            _stack.push_back(std::move(_alt.l));
          }
          if (_alt.r) {
            _stack.push_back(std::move(_alt.r));
          }
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node) {
          _drain(*_node);
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, tree<T1> &, T2 &, T1 &, tree<T1> &,
                                   T2 &>
  static T2 tree_rect(T2 f, F1 &&f0, const tree<T1> &t) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[a0, a1, a2] = std::get<typename tree<T1>::Node>(t.v());
      return f0(*a0, tree_rect<T1, T2>(f, f0, *a0), a1, *a2,
                tree_rect<T1, T2>(f, f0, *a2));
    }
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, tree<T1> &, T2 &, T1 &, tree<T1> &,
                                   T2 &>
  static T2 tree_rec(T2 f, F1 &&f0, const tree<T1> &t) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[a0, a1, a2] = std::get<typename tree<T1>::Node>(t.v());
      return f0(*a0, tree_rec<T1, T2>(f, f0, *a0), a1, *a2,
                tree_rec<T1, T2>(f, f0, *a2));
    }
  }

  static tree<uint64_t> depth_tree(uint64_t n);

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static tree<T2> tree_map(F0 &&f, const tree<T1> &t) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
      return tree<T2>::leaf();
    } else {
      const auto &[a0, a1, a2] = std::get<typename tree<T1>::Node>(t.v());
      return tree<T2>::node(tree_map<T1, T2>(f, *a0), f(a1),
                            tree_map<T1, T2>(f, *a2));
    }
  }

  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, T2 &, T1 &, T2 &>
  static T2 tree_fold(T2 base, F1 &&f, const tree<T1> &t) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
      return base;
    } else {
      const auto &[a0, a1, a2] = std::get<typename tree<T1>::Node>(t.v());
      return f(tree_fold<T1, T2>(base, f, *a0), a1,
               tree_fold<T1, T2>(base, f, *a2));
    }
  }

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, T1 &, T2 &>
  static tree<T3> tree_zip_with(F0 &&f, const tree<T1> &t1,
                                const tree<T2> &t2) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(t1.v())) {
      return tree<T3>::leaf();
    } else {
      const auto &[a0, a1, a2] = std::get<typename tree<T1>::Node>(t1.v());
      if (std::holds_alternative<typename tree<T2>::Leaf>(t2.v())) {
        return tree<T3>::leaf();
      } else {
        const auto &[a00, a10, a20] = std::get<typename tree<T2>::Node>(t2.v());
        return tree<T3>::node(tree_zip_with<T1, T2, T3>(f, *a0, *a00),
                              f(a1, a10),
                              tree_zip_with<T1, T2, T3>(f, *a2, *a20));
      }
    }
  }

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<std::pair<T3, T2>, F0 &, T3 &, T1 &>
  static std::pair<T3, tree<T2>> tree_map_accum(F0 &&f, T3 acc,
                                                const tree<T1> &t) {
    if (std::holds_alternative<typename tree<T1>::Leaf>(t.v())) {
      return std::make_pair(std::move(acc), tree<T2>::leaf());
    } else {
      const auto &[a0, a1, a2] = std::get<typename tree<T1>::Node>(t.v());
      auto _cs = tree_map_accum<T1, T2, T3>(f, std::move(acc), *a0);
      const T3 &acc1 = _cs.first;
      const tree<T2> &l_ = _cs.second;
      auto _cs1 = f(acc1, a1);
      const T3 &acc2 = _cs1.first;
      const T2 &x_ = _cs1.second;
      auto _cs2 = tree_map_accum<T1, T2, T3>(f, std::move(_cs1.first), *a2);
      const T3 &acc3 = _cs2.first;
      const tree<T2> &r_ = _cs2.second;
      return std::make_pair(std::move(_cs2.first), tree<T2>::node(l_, x_, r_));
    }
  }

  static inline const tree<uint64_t> small_tree = tree<uint64_t>::node(
      tree<uint64_t>::node(
          tree<uint64_t>::node(tree<uint64_t>::leaf(), UINT64_C(1),
                               tree<uint64_t>::leaf()),
          UINT64_C(2),
          tree<uint64_t>::node(tree<uint64_t>::leaf(), UINT64_C(3),
                               tree<uint64_t>::leaf())),
      UINT64_C(4),
      tree<uint64_t>::node(
          tree<uint64_t>::node(tree<uint64_t>::leaf(), UINT64_C(5),
                               tree<uint64_t>::leaf()),
          UINT64_C(6),
          tree<uint64_t>::node(tree<uint64_t>::leaf(), UINT64_C(7),
                               tree<uint64_t>::leaf())));
  static inline const tree<uint64_t> mapped = tree_map<uint64_t, uint64_t>(
      [](uint64_t x) { return (x * UINT64_C(2)); }, small_tree);
  static inline const uint64_t folded = tree_fold<uint64_t, uint64_t>(
      UINT64_C(0),
      [](uint64_t l, uint64_t x, uint64_t r) { return ((l + x) + r); },
      small_tree);
  static inline const tree<uint64_t> zipped =
      tree_zip_with<uint64_t, uint64_t, uint64_t>(
          [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); },
          small_tree, small_tree);
  static inline const std::pair<uint64_t, tree<uint64_t>> accum =
      tree_map_accum<uint64_t, uint64_t, uint64_t>(
          [](uint64_t s, uint64_t x) { return std::make_pair((s + x), s); },
          UINT64_C(0), small_tree);
  static inline const tree<uint64_t> deep = depth_tree(UINT64_C(50000));
};

#endif // INCLUDED_HOF_TREE_LOOPIFY
