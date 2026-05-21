#ifndef INCLUDED_NUMERAL_EDGE
#define INCLUDED_NUMERAL_EDGE

#include <cstdint>
#include <memory>
#include <optional>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  List(const List<A> &_other) : v_(std::move(_other.clone().v_)) {}

  List(List<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  List<A> clone() const {
    List<A> _out{};

    struct _CloneFrame {
      const List<A> *_src;
      List<A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<A> *_src = _frame._src;
      List<A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->v_ = Cons{_alt.a, _alt.l ? std::make_shared<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.l) {
          _stack.push_back({_alt.l.get(), _dst_alt.l.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a), l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
        if (_alt.l) {
          _stack.push_back(std::move(_alt.l));
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

struct Uint {
  // TYPES
  struct Nil {};

  struct D0 {
    std::shared_ptr<Uint> a0;
  };

  struct D1 {
    std::shared_ptr<Uint> a0;
  };

  struct D2 {
    std::shared_ptr<Uint> a0;
  };

  struct D3 {
    std::shared_ptr<Uint> a0;
  };

  struct D4 {
    std::shared_ptr<Uint> a0;
  };

  struct D5 {
    std::shared_ptr<Uint> a0;
  };

  struct D6 {
    std::shared_ptr<Uint> a0;
  };

  struct D7 {
    std::shared_ptr<Uint> a0;
  };

  struct D8 {
    std::shared_ptr<Uint> a0;
  };

  struct D9 {
    std::shared_ptr<Uint> a0;
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
        _dst->v_ = D0{_alt.a0 ? std::make_shared<Uint>() : nullptr};
        auto &_dst_alt = std::get<D0>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<D1>(_src->v())) {
        const auto &_alt = std::get<D1>(_src->v());
        _dst->v_ = D1{_alt.a0 ? std::make_shared<Uint>() : nullptr};
        auto &_dst_alt = std::get<D1>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<D2>(_src->v())) {
        const auto &_alt = std::get<D2>(_src->v());
        _dst->v_ = D2{_alt.a0 ? std::make_shared<Uint>() : nullptr};
        auto &_dst_alt = std::get<D2>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<D3>(_src->v())) {
        const auto &_alt = std::get<D3>(_src->v());
        _dst->v_ = D3{_alt.a0 ? std::make_shared<Uint>() : nullptr};
        auto &_dst_alt = std::get<D3>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<D4>(_src->v())) {
        const auto &_alt = std::get<D4>(_src->v());
        _dst->v_ = D4{_alt.a0 ? std::make_shared<Uint>() : nullptr};
        auto &_dst_alt = std::get<D4>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<D5>(_src->v())) {
        const auto &_alt = std::get<D5>(_src->v());
        _dst->v_ = D5{_alt.a0 ? std::make_shared<Uint>() : nullptr};
        auto &_dst_alt = std::get<D5>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<D6>(_src->v())) {
        const auto &_alt = std::get<D6>(_src->v());
        _dst->v_ = D6{_alt.a0 ? std::make_shared<Uint>() : nullptr};
        auto &_dst_alt = std::get<D6>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<D7>(_src->v())) {
        const auto &_alt = std::get<D7>(_src->v());
        _dst->v_ = D7{_alt.a0 ? std::make_shared<Uint>() : nullptr};
        auto &_dst_alt = std::get<D7>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<D8>(_src->v())) {
        const auto &_alt = std::get<D8>(_src->v());
        _dst->v_ = D8{_alt.a0 ? std::make_shared<Uint>() : nullptr};
        auto &_dst_alt = std::get<D8>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else {
        const auto &_alt = std::get<D9>(_src->v());
        _dst->v_ = D9{_alt.a0 ? std::make_shared<Uint>() : nullptr};
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
    return Uint(D0{std::make_shared<Uint>(std::move(a0))});
  }

  static Uint d1(Uint a0) {
    return Uint(D1{std::make_shared<Uint>(std::move(a0))});
  }

  static Uint d2(Uint a0) {
    return Uint(D2{std::make_shared<Uint>(std::move(a0))});
  }

  static Uint d3(Uint a0) {
    return Uint(D3{std::make_shared<Uint>(std::move(a0))});
  }

  static Uint d4(Uint a0) {
    return Uint(D4{std::make_shared<Uint>(std::move(a0))});
  }

  static Uint d5(Uint a0) {
    return Uint(D5{std::make_shared<Uint>(std::move(a0))});
  }

  static Uint d6(Uint a0) {
    return Uint(D6{std::make_shared<Uint>(std::move(a0))});
  }

  static Uint d7(Uint a0) {
    return Uint(D7{std::make_shared<Uint>(std::move(a0))});
  }

  static Uint d8(Uint a0) {
    return Uint(D8{std::make_shared<Uint>(std::move(a0))});
  }

  static Uint d9(Uint a0) {
    return Uint(D9{std::make_shared<Uint>(std::move(a0))});
  }

  // MANIPULATORS
  ~Uint() {
    std::vector<std::shared_ptr<Uint>> _stack{};
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
    std::shared_ptr<Uint0> a0;
  };

  struct D11 {
    std::shared_ptr<Uint0> a0;
  };

  struct D12 {
    std::shared_ptr<Uint0> a0;
  };

  struct D13 {
    std::shared_ptr<Uint0> a0;
  };

  struct D14 {
    std::shared_ptr<Uint0> a0;
  };

  struct D15 {
    std::shared_ptr<Uint0> a0;
  };

  struct D16 {
    std::shared_ptr<Uint0> a0;
  };

  struct D17 {
    std::shared_ptr<Uint0> a0;
  };

  struct D18 {
    std::shared_ptr<Uint0> a0;
  };

  struct D19 {
    std::shared_ptr<Uint0> a0;
  };

  struct Da {
    std::shared_ptr<Uint0> a0;
  };

  struct Db {
    std::shared_ptr<Uint0> a0;
  };

  struct Dc {
    std::shared_ptr<Uint0> a0;
  };

  struct Dd {
    std::shared_ptr<Uint0> a0;
  };

  struct De {
    std::shared_ptr<Uint0> a0;
  };

  struct Df {
    std::shared_ptr<Uint0> a0;
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
        _dst->v_ = D10{_alt.a0 ? std::make_shared<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D10>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<D11>(_src->v())) {
        const auto &_alt = std::get<D11>(_src->v());
        _dst->v_ = D11{_alt.a0 ? std::make_shared<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D11>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<D12>(_src->v())) {
        const auto &_alt = std::get<D12>(_src->v());
        _dst->v_ = D12{_alt.a0 ? std::make_shared<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D12>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<D13>(_src->v())) {
        const auto &_alt = std::get<D13>(_src->v());
        _dst->v_ = D13{_alt.a0 ? std::make_shared<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D13>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<D14>(_src->v())) {
        const auto &_alt = std::get<D14>(_src->v());
        _dst->v_ = D14{_alt.a0 ? std::make_shared<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D14>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<D15>(_src->v())) {
        const auto &_alt = std::get<D15>(_src->v());
        _dst->v_ = D15{_alt.a0 ? std::make_shared<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D15>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<D16>(_src->v())) {
        const auto &_alt = std::get<D16>(_src->v());
        _dst->v_ = D16{_alt.a0 ? std::make_shared<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D16>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<D17>(_src->v())) {
        const auto &_alt = std::get<D17>(_src->v());
        _dst->v_ = D17{_alt.a0 ? std::make_shared<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D17>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<D18>(_src->v())) {
        const auto &_alt = std::get<D18>(_src->v());
        _dst->v_ = D18{_alt.a0 ? std::make_shared<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D18>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<D19>(_src->v())) {
        const auto &_alt = std::get<D19>(_src->v());
        _dst->v_ = D19{_alt.a0 ? std::make_shared<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D19>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<Da>(_src->v())) {
        const auto &_alt = std::get<Da>(_src->v());
        _dst->v_ = Da{_alt.a0 ? std::make_shared<Uint0>() : nullptr};
        auto &_dst_alt = std::get<Da>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<Db>(_src->v())) {
        const auto &_alt = std::get<Db>(_src->v());
        _dst->v_ = Db{_alt.a0 ? std::make_shared<Uint0>() : nullptr};
        auto &_dst_alt = std::get<Db>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<Dc>(_src->v())) {
        const auto &_alt = std::get<Dc>(_src->v());
        _dst->v_ = Dc{_alt.a0 ? std::make_shared<Uint0>() : nullptr};
        auto &_dst_alt = std::get<Dc>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<Dd>(_src->v())) {
        const auto &_alt = std::get<Dd>(_src->v());
        _dst->v_ = Dd{_alt.a0 ? std::make_shared<Uint0>() : nullptr};
        auto &_dst_alt = std::get<Dd>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else if (std::holds_alternative<De>(_src->v())) {
        const auto &_alt = std::get<De>(_src->v());
        _dst->v_ = De{_alt.a0 ? std::make_shared<Uint0>() : nullptr};
        auto &_dst_alt = std::get<De>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      } else {
        const auto &_alt = std::get<Df>(_src->v());
        _dst->v_ = Df{_alt.a0 ? std::make_shared<Uint0>() : nullptr};
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
    return Uint0(D10{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 d11(Uint0 a0) {
    return Uint0(D11{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 d12(Uint0 a0) {
    return Uint0(D12{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 d13(Uint0 a0) {
    return Uint0(D13{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 d14(Uint0 a0) {
    return Uint0(D14{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 d15(Uint0 a0) {
    return Uint0(D15{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 d16(Uint0 a0) {
    return Uint0(D16{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 d17(Uint0 a0) {
    return Uint0(D17{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 d18(Uint0 a0) {
    return Uint0(D18{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 d19(Uint0 a0) {
    return Uint0(D19{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 da(Uint0 a0) {
    return Uint0(Da{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 db(Uint0 a0) {
    return Uint0(Db{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 dc(Uint0 a0) {
    return Uint0(Dc{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 dd(Uint0 a0) {
    return Uint0(Dd{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 de(Uint0 a0) {
    return Uint0(De{std::make_shared<Uint0>(std::move(a0))});
  }

  static Uint0 df(Uint0 a0) {
    return Uint0(Df{std::make_shared<Uint0>(std::move(a0))});
  }

  // MANIPULATORS
  ~Uint0() {
    std::vector<std::shared_ptr<Uint0>> _stack{};
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

struct NumeralEdge {
  /// 1. Zero
  static inline const uint64_t nat_zero = UINT64_C(0);
  static inline const unsigned int n_zero = 0u;
  static inline const int64_t z_zero = INT64_C(0);
  /// 2. Small values
  static inline const uint64_t nat_one = UINT64_C(1);
  static inline const uint64_t nat_ten = UINT64_C(10);
  static inline const int64_t z_neg = INT64_C(-5);
  static inline const int64_t z_neg_one = INT64_C(-1);
  /// 3. Moderate values
  static inline const uint64_t nat_hundred = UINT64_C(100);
  static inline const int64_t z_thousand = INT64_C(1000);
  static inline const unsigned int n_large = 65535u;
  /// 4. Powers of 2
  static inline const uint64_t nat_pow2_8 = UINT64_C(256);
  static inline const uint64_t nat_pow2_16 = UINT64_C(65536);
  static inline const int64_t z_pow2_30 = INT64_C(1073741824);
  /// 5. Numerals in arithmetic expressions
  static inline const uint64_t add_numerals = (UINT64_C(100) + UINT64_C(200));
  static inline const int64_t mul_numerals = (INT64_C(10) * INT64_C(20));
  static inline const int64_t sub_numerals = (INT64_C(100) - INT64_C(1));
  /// 6. Numeral as function argument
  static uint64_t take_nat(uint64_t n);
  static inline const uint64_t test_arg = take_nat(UINT64_C(42));
  /// 7. Numeral in list
  static inline const List<uint64_t> nat_list = List<uint64_t>::cons(
      UINT64_C(1), List<uint64_t>::cons(
                       UINT64_C(2), List<uint64_t>::cons(
                                        UINT64_C(3), List<uint64_t>::nil())));
  /// 8. Numeral in option
  static inline const std::optional<uint64_t> some_nat =
      std::make_optional<uint64_t>(UINT64_C(99));
  /// 9. Numeral in pair
  static inline const std::pair<uint64_t, uint64_t> nat_pair =
      std::make_pair(UINT64_C(10), UINT64_C(20));
  /// 10. Numeral in match
  static uint64_t classify(uint64_t n);
  /// 11. Comparison with numeral
  static bool is_big(uint64_t n);
  /// 12. Multiple Z values in one function
  static inline const int64_t z_arith =
      (INT64_C(10) + (INT64_C(3) * INT64_C(7)));
  /// 13. Negative Z in a pair
  static inline const std::pair<int64_t, int64_t> z_pair =
      std::make_pair(INT64_C(-42), INT64_C(42));

  /// 14. N conversion
  static inline const uint64_t n_to_nat_test = static_cast<unsigned int>(255u);
};

#endif // INCLUDED_NUMERAL_EDGE
