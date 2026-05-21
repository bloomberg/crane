#ifndef INCLUDED_VALIDATED_PUMP_DELIVERY_TRACE
#define INCLUDED_VALIDATED_PUMP_DELIVERY_TRACE

#include <memory>
#include <optional>
#include <type_traits>
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

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, A &>
  bool forallb(F0 &&f) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return true;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return (f(a0) && a1->forallb(f));
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &, A &>
  T1 fold_left(F0 &&f, T1 a0) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return a0;
    } else {
      const auto &[a1, a2] = std::get<typename List<A>::Cons>(this->v());
      return a2->template fold_left<T1>(f, f(a0, a1));
    }
  }

  uint64_t length() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return (a1->length() + 1);
    }
  }
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

struct ValidatedPumpDeliveryTraceCase {
  struct Mg_dL {
    uint64_t mg_dL_val;

    // ACCESSORS
    Mg_dL clone() const { return Mg_dL{this->mg_dL_val}; }
  };

  struct Grams {
    uint64_t grams_val;

    // ACCESSORS
    Grams clone() const { return Grams{this->grams_val}; }
  };

  using Carbs_g = Grams;
  using Minutes = uint64_t;
  using DIA_minutes = uint64_t;
  using Insulin_twentieth = uint64_t;
  static inline const uint64_t ONE_UNIT = UINT64_C(20);
  static inline const uint64_t BG_LEVEL2_HYPO = UINT64_C(54);
  static inline const uint64_t BG_HYPO = UINT64_C(70);
  static inline const uint64_t BG_HYPER = UINT64_C(180);
  static inline const uint64_t BG_METER_MIN = UINT64_C(20);
  static inline const uint64_t BG_METER_MAX = UINT64_C(600);
  static inline const uint64_t CARBS_SANITY_MAX = UINT64_C(200);
  static bool bg_in_meter_range(const Mg_dL &bg);
  static bool carbs_reasonable(const Grams &carbs);

  struct Config {
    uint64_t cfg_bg_rise_per_gram;
    uint64_t cfg_conservative_cob_absorption_percent;
    uint64_t cfg_suspend_threshold_mg_dl;
    uint64_t cfg_stacking_warning_threshold_min;
    uint64_t cfg_iob_high_threshold_twentieths;

    // ACCESSORS
    Config clone() const {
      return Config{this->cfg_bg_rise_per_gram,
                    this->cfg_conservative_cob_absorption_percent,
                    this->cfg_suspend_threshold_mg_dl,
                    this->cfg_stacking_warning_threshold_min,
                    this->cfg_iob_high_threshold_twentieths};
    }
  };

  static inline const Config default_config = Config{
      UINT64_C(4), UINT64_C(30), UINT64_C(80), UINT64_C(60), UINT64_C(200)};
  enum class ActivityState {
    ACTIVITY_NORMAL,
    ACTIVITY_LIGHTEXERCISE,
    ACTIVITY_MODERATEEXERCISE,
    ACTIVITY_INTENSEEXERCISE,
    ACTIVITY_ILLNESS,
    ACTIVITY_STRESS
  };

  template <typename T1>
  static T1 ActivityState_rect(T1 f, T1 f0, T1 f1, T1 f2, T1 f3, T1 f4,
                               ActivityState a) {
    switch (a) {
    case ActivityState::ACTIVITY_NORMAL: {
      return f;
    }
    case ActivityState::ACTIVITY_LIGHTEXERCISE: {
      return f0;
    }
    case ActivityState::ACTIVITY_MODERATEEXERCISE: {
      return f1;
    }
    case ActivityState::ACTIVITY_INTENSEEXERCISE: {
      return f2;
    }
    case ActivityState::ACTIVITY_ILLNESS: {
      return f3;
    }
    case ActivityState::ACTIVITY_STRESS: {
      return f4;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 ActivityState_rec(T1 f, T1 f0, T1 f1, T1 f2, T1 f3, T1 f4,
                              ActivityState a) {
    switch (a) {
    case ActivityState::ACTIVITY_NORMAL: {
      return f;
    }
    case ActivityState::ACTIVITY_LIGHTEXERCISE: {
      return f0;
    }
    case ActivityState::ACTIVITY_MODERATEEXERCISE: {
      return f1;
    }
    case ActivityState::ACTIVITY_INTENSEEXERCISE: {
      return f2;
    }
    case ActivityState::ACTIVITY_ILLNESS: {
      return f3;
    }
    case ActivityState::ACTIVITY_STRESS: {
      return f4;
    }
    default:
      std::unreachable();
    }
  }

  static uint64_t isf_activity_modifier(ActivityState state);
  static uint64_t icr_activity_modifier(ActivityState state);

  struct FaultStatus {
    // TYPES
    struct Fault_None {};

    struct Fault_Occlusion {};

    struct Fault_LowReservoir {
      uint64_t a0;
    };

    struct Fault_BatteryLow {};

    struct Fault_Unknown {};

    using variant_t =
        std::variant<Fault_None, Fault_Occlusion, Fault_LowReservoir,
                     Fault_BatteryLow, Fault_Unknown>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    FaultStatus() {}

    explicit FaultStatus(Fault_None _v) : v_(_v) {}

    explicit FaultStatus(Fault_Occlusion _v) : v_(_v) {}

    explicit FaultStatus(Fault_LowReservoir _v) : v_(std::move(_v)) {}

    explicit FaultStatus(Fault_BatteryLow _v) : v_(_v) {}

    explicit FaultStatus(Fault_Unknown _v) : v_(_v) {}

    FaultStatus(const FaultStatus &_other) : v_(std::move(_other.clone().v_)) {}

    FaultStatus(FaultStatus &&_other) noexcept : v_(std::move(_other.v_)) {}

    FaultStatus &operator=(const FaultStatus &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    FaultStatus &operator=(FaultStatus &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    FaultStatus clone() const {
      if (std::holds_alternative<Fault_None>(this->v())) {
        return FaultStatus(Fault_None{});
      } else if (std::holds_alternative<Fault_Occlusion>(this->v())) {
        return FaultStatus(Fault_Occlusion{});
      } else if (std::holds_alternative<Fault_LowReservoir>(this->v())) {
        const auto &[a0] = std::get<Fault_LowReservoir>(this->v());
        return FaultStatus(Fault_LowReservoir{a0});
      } else if (std::holds_alternative<Fault_BatteryLow>(this->v())) {
        return FaultStatus(Fault_BatteryLow{});
      } else {
        return FaultStatus(Fault_Unknown{});
      }
    }

    // CREATORS
    static FaultStatus fault_none() { return FaultStatus(Fault_None{}); }

    static FaultStatus fault_occlusion() {
      return FaultStatus(Fault_Occlusion{});
    }

    static FaultStatus fault_lowreservoir(uint64_t a0) {
      return FaultStatus(Fault_LowReservoir{a0});
    }

    static FaultStatus fault_batterylow() {
      return FaultStatus(Fault_BatteryLow{});
    }

    static FaultStatus fault_unknown() { return FaultStatus(Fault_Unknown{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    bool fault_blocks_bolus() const {
      if (std::holds_alternative<typename FaultStatus::Fault_None>(this->v())) {
        return false;
      } else if (std::holds_alternative<
                     typename FaultStatus::Fault_LowReservoir>(this->v())) {
        const auto &[a0] =
            std::get<typename FaultStatus::Fault_LowReservoir>(this->v());
        return a0 < UINT64_C(10);
      } else if (std::holds_alternative<typename FaultStatus::Fault_BatteryLow>(
                     this->v())) {
        return false;
      } else {
        return true;
      }
    }

    template <typename T1, typename F2>
      requires std::is_invocable_r_v<T1, F2 &, uint64_t &>
    T1 FaultStatus_rec(T1 f, T1 f0, F2 &&f1, T1 f2, T1 f3) const {
      if (std::holds_alternative<typename FaultStatus::Fault_None>(this->v())) {
        return f;
      } else if (std::holds_alternative<typename FaultStatus::Fault_Occlusion>(
                     this->v())) {
        return f0;
      } else if (std::holds_alternative<
                     typename FaultStatus::Fault_LowReservoir>(this->v())) {
        const auto &[a0] =
            std::get<typename FaultStatus::Fault_LowReservoir>(this->v());
        return f1(a0);
      } else if (std::holds_alternative<typename FaultStatus::Fault_BatteryLow>(
                     this->v())) {
        return f2;
      } else {
        return f3;
      }
    }

    template <typename T1, typename F2>
      requires std::is_invocable_r_v<T1, F2 &, uint64_t &>
    T1 FaultStatus_rect(T1 f, T1 f0, F2 &&f1, T1 f2, T1 f3) const {
      if (std::holds_alternative<typename FaultStatus::Fault_None>(this->v())) {
        return f;
      } else if (std::holds_alternative<typename FaultStatus::Fault_Occlusion>(
                     this->v())) {
        return f0;
      } else if (std::holds_alternative<
                     typename FaultStatus::Fault_LowReservoir>(this->v())) {
        const auto &[a0] =
            std::get<typename FaultStatus::Fault_LowReservoir>(this->v());
        return f1(a0);
      } else if (std::holds_alternative<typename FaultStatus::Fault_BatteryLow>(
                     this->v())) {
        return f2;
      } else {
        return f3;
      }
    }
  };
  enum class InsulinType { INSULIN_HUMALOG, INSULIN_ASPART, INSULIN_LISPRO };

  template <typename T1>
  static T1 InsulinType_rect(T1 f, T1 f0, T1 f1, InsulinType i) {
    switch (i) {
    case InsulinType::INSULIN_HUMALOG: {
      return f;
    }
    case InsulinType::INSULIN_ASPART: {
      return f0;
    }
    case InsulinType::INSULIN_LISPRO: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 InsulinType_rec(T1 f, T1 f0, T1 f1, InsulinType i) {
    switch (i) {
    case InsulinType::INSULIN_HUMALOG: {
      return f;
    }
    case InsulinType::INSULIN_ASPART: {
      return f0;
    }
    case InsulinType::INSULIN_LISPRO: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  static Minutes peak_time(InsulinType itype, uint64_t _x);

  struct BolusEvent {
    uint64_t be_dose_twentieths;
    Minutes be_time_minutes;

    // ACCESSORS
    BolusEvent clone() const {
      return BolusEvent{this->be_dose_twentieths, this->be_time_minutes};
    }
  };

  static uint64_t div_ceil(uint64_t a, uint64_t b);
  static bool event_time_valid(uint64_t now, const BolusEvent &event);
  static bool history_times_valid(uint64_t now, const List<BolusEvent> &events);
  static bool history_sorted_from(uint64_t prev,
                                  const List<BolusEvent> &events);
  static bool history_sorted_desc(const List<BolusEvent> &events);
  static bool history_valid(uint64_t now, const List<BolusEvent> &events);
  static uint64_t bilinear_iob_fraction(uint64_t elapsed, uint64_t dia,
                                        InsulinType itype);
  static Insulin_twentieth bilinear_iob_from_bolus(uint64_t now,
                                                   const BolusEvent &event,
                                                   uint64_t dia,
                                                   InsulinType itype);
  static Insulin_twentieth total_bilinear_iob(uint64_t now,
                                              const List<BolusEvent> &events,
                                              uint64_t dia, InsulinType itype);
  static Mg_dL apply_sensor_margin(Mg_dL bg, const Mg_dL &target);
  static uint64_t adjusted_isf_tenths(const Mg_dL &bg,
                                      uint64_t base_isf_tenths);
  static Insulin_twentieth correction_twentieths_full(uint64_t _x,
                                                      const Mg_dL &current_bg,
                                                      const Mg_dL &target_bg,
                                                      uint64_t base_isf_tenths);
  static Insulin_twentieth
  apply_reverse_correction_twentieths(uint64_t carb, const Mg_dL &current_bg,
                                      const Mg_dL &target_bg,
                                      uint64_t isf_tenths);

  struct SuspendDecision {
    // TYPES
    struct Suspend_None {};

    struct Suspend_Reduce {
      Insulin_twentieth a0;
    };

    struct Suspend_Withhold {};

    using variant_t =
        std::variant<Suspend_None, Suspend_Reduce, Suspend_Withhold>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    SuspendDecision() {}

    explicit SuspendDecision(Suspend_None _v) : v_(_v) {}

    explicit SuspendDecision(Suspend_Reduce _v) : v_(std::move(_v)) {}

    explicit SuspendDecision(Suspend_Withhold _v) : v_(_v) {}

    SuspendDecision(const SuspendDecision &_other)
        : v_(std::move(_other.clone().v_)) {}

    SuspendDecision(SuspendDecision &&_other) noexcept
        : v_(std::move(_other.v_)) {}

    SuspendDecision &operator=(const SuspendDecision &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    SuspendDecision &operator=(SuspendDecision &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    SuspendDecision clone() const {
      if (std::holds_alternative<Suspend_None>(this->v())) {
        return SuspendDecision(Suspend_None{});
      } else if (std::holds_alternative<Suspend_Reduce>(this->v())) {
        const auto &[a0] = std::get<Suspend_Reduce>(this->v());
        return SuspendDecision(Suspend_Reduce{a0});
      } else {
        return SuspendDecision(Suspend_Withhold{});
      }
    }

    // CREATORS
    static SuspendDecision suspend_none() {
      return SuspendDecision(Suspend_None{});
    }

    static SuspendDecision suspend_reduce(Insulin_twentieth a0) {
      return SuspendDecision(Suspend_Reduce{std::move(a0)});
    }

    static SuspendDecision suspend_withhold() {
      return SuspendDecision(Suspend_Withhold{});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &>
  static T1 SuspendDecision_rect(T1 f, F1 &&f0, T1 f1,
                                 const SuspendDecision &s) {
    if (std::holds_alternative<typename SuspendDecision::Suspend_None>(s.v())) {
      return f;
    } else if (std::holds_alternative<typename SuspendDecision::Suspend_Reduce>(
                   s.v())) {
      const auto &[a0] =
          std::get<typename SuspendDecision::Suspend_Reduce>(s.v());
      return f0(a0);
    } else {
      return f1;
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &>
  static T1 SuspendDecision_rec(T1 f, F1 &&f0, T1 f1,
                                const SuspendDecision &s) {
    if (std::holds_alternative<typename SuspendDecision::Suspend_None>(s.v())) {
      return f;
    } else if (std::holds_alternative<typename SuspendDecision::Suspend_Reduce>(
                   s.v())) {
      const auto &[a0] =
          std::get<typename SuspendDecision::Suspend_Reduce>(s.v());
      return f0(a0);
    } else {
      return f1;
    }
  }

  static uint64_t predict_bg_drop_tenths(uint64_t iob_twentieths,
                                         uint64_t isf_tenths);
  static uint64_t conservative_cob_rise(const Config &cfg, uint64_t cob_grams);
  static uint64_t predicted_eventual_bg_tenths(const Config &cfg,
                                               const Mg_dL &current_bg,
                                               uint64_t iob_twentieths,
                                               uint64_t cob_grams,
                                               uint64_t isf_tenths);
  static SuspendDecision
  suspend_check_tenths_with_cob(const Config &cfg, const Mg_dL &current_bg,
                                uint64_t iob_twentieths, uint64_t cob_grams,
                                uint64_t isf_tenths, uint64_t proposed);
  static Insulin_twentieth apply_suspend(uint64_t proposed,
                                         const SuspendDecision &decision);
  static Insulin_twentieth pediatric_max_twentieths(uint64_t weight_kg);
  static Insulin_twentieth cap_pediatric(uint64_t bolus, uint64_t weight_kg);

  struct PrecisionParams {
    uint64_t prec_icr_tenths;
    uint64_t prec_isf_tenths;
    Mg_dL prec_target_bg;
    DIA_minutes prec_dia;
    InsulinType prec_insulin_type;

    // ACCESSORS
    PrecisionParams clone() const {
      return PrecisionParams{this->prec_icr_tenths, this->prec_isf_tenths,
                             this->prec_target_bg.clone(), this->prec_dia,
                             this->prec_insulin_type};
    }
  };

  static bool prec_params_valid(const PrecisionParams &p);

  struct PrecisionInput {
    Carbs_g pi_carbs_g;
    Mg_dL pi_current_bg;
    Minutes pi_now;
    List<BolusEvent> pi_bolus_history;
    ActivityState pi_activity;
    bool pi_use_sensor_margin;
    FaultStatus pi_fault;
    std::optional<uint64_t> pi_weight_kg;

    // ACCESSORS
    PrecisionInput clone() const {
      return PrecisionInput{
          this->pi_carbs_g,       this->pi_current_bg.clone(),
          this->pi_now,           this->pi_bolus_history.clone(),
          this->pi_activity,      this->pi_use_sensor_margin,
          this->pi_fault.clone(), this->pi_weight_kg};
    }
  };

  static Insulin_twentieth carb_bolus_twentieths(uint64_t carbs_g,
                                                 uint64_t icr_tenths);
  static Insulin_twentieth
  calculate_precision_bolus(const PrecisionInput &input,
                            const PrecisionParams &params);
  static bool time_reasonable(uint64_t now);
  static bool history_extraction_safe(const List<BolusEvent> &events);
  static uint64_t iob_high_threshold(const Config &cfg);
  static bool iob_dangerously_high(uint64_t iob);

  struct PrecisionResult {
    // TYPES
    struct PrecOK {
      Insulin_twentieth a0;
      bool a1;
    };

    struct PrecError {
      uint64_t a0;
    };

    using variant_t = std::variant<PrecOK, PrecError>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    PrecisionResult() {}

    explicit PrecisionResult(PrecOK _v) : v_(std::move(_v)) {}

    explicit PrecisionResult(PrecError _v) : v_(std::move(_v)) {}

    PrecisionResult(const PrecisionResult &_other)
        : v_(std::move(_other.clone().v_)) {}

    PrecisionResult(PrecisionResult &&_other) noexcept
        : v_(std::move(_other.v_)) {}

    PrecisionResult &operator=(const PrecisionResult &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    PrecisionResult &operator=(PrecisionResult &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    PrecisionResult clone() const {
      if (std::holds_alternative<PrecOK>(this->v())) {
        const auto &[a0, a1] = std::get<PrecOK>(this->v());
        return PrecisionResult(PrecOK{a0, a1});
      } else {
        const auto &[a0] = std::get<PrecError>(this->v());
        return PrecisionResult(PrecError{a0});
      }
    }

    // CREATORS
    static PrecisionResult precok(Insulin_twentieth a0, bool a1) {
      return PrecisionResult(PrecOK{std::move(a0), a1});
    }

    static PrecisionResult precerror(uint64_t a0) {
      return PrecisionResult(PrecError{a0});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    bool result_modified() const {
      if (std::holds_alternative<typename PrecisionResult::PrecOK>(this->v())) {
        const auto &[a0, a1] =
            std::get<typename PrecisionResult::PrecOK>(this->v());
        return a1;
      } else {
        return false;
      }
    }

    uint64_t precision_result_code() const {
      if (std::holds_alternative<typename PrecisionResult::PrecOK>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0] =
            std::get<typename PrecisionResult::PrecError>(this->v());
        return a0;
      }
    }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, bool &> &&
             std::is_invocable_r_v<T1, F1 &, uint64_t &>
  static T1 PrecisionResult_rect(F0 &&f, F1 &&f0, const PrecisionResult &p) {
    if (std::holds_alternative<typename PrecisionResult::PrecOK>(p.v())) {
      const auto &[a0, a1] = std::get<typename PrecisionResult::PrecOK>(p.v());
      return f(a0, a1);
    } else {
      const auto &[a0] = std::get<typename PrecisionResult::PrecError>(p.v());
      return f0(a0);
    }
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, bool &> &&
             std::is_invocable_r_v<T1, F1 &, uint64_t &>
  static T1 PrecisionResult_rec(F0 &&f, F1 &&f0, const PrecisionResult &p) {
    if (std::holds_alternative<typename PrecisionResult::PrecOK>(p.v())) {
      const auto &[a0, a1] = std::get<typename PrecisionResult::PrecOK>(p.v());
      return f(a0, a1);
    } else {
      const auto &[a0] = std::get<typename PrecisionResult::PrecError>(p.v());
      return f0(a0);
    }
  }

  static inline const uint64_t prec_error_invalid_params = UINT64_C(1);
  static inline const uint64_t prec_error_invalid_input = UINT64_C(2);
  static inline const uint64_t prec_error_hypo = UINT64_C(3);
  static inline const uint64_t prec_error_invalid_history = UINT64_C(4);
  static inline const uint64_t prec_error_invalid_time = UINT64_C(5);
  static inline const uint64_t prec_error_stacking = UINT64_C(6);
  static inline const uint64_t prec_error_fault = UINT64_C(7);
  static inline const uint64_t prec_error_tdd_exceeded = UINT64_C(8);
  static inline const uint64_t prec_error_iob_high = UINT64_C(9);
  static inline const uint64_t prec_error_extraction_unsafe = UINT64_C(10);
  static bool bolus_too_soon(uint64_t now, const List<BolusEvent> &history);
  static Insulin_twentieth cap_twentieths(uint64_t t);
  static PrecisionResult
  validated_precision_bolus(PrecisionInput input,
                            const PrecisionParams &params);
  static std::optional<Insulin_twentieth>
  prec_result_twentieths(const PrecisionResult &r);

  struct MmolPrecisionInput {
    Carbs_g mpi_carbs_g;
    uint64_t mpi_current_bg_mmol_tenths;
    Minutes mpi_now;
    List<BolusEvent> mpi_bolus_history;
    ActivityState mpi_activity;
    bool mpi_use_sensor_margin;
    FaultStatus mpi_fault;
    std::optional<uint64_t> mpi_weight_kg;

    // ACCESSORS
    MmolPrecisionInput clone() const {
      return MmolPrecisionInput{
          this->mpi_carbs_g,       this->mpi_current_bg_mmol_tenths,
          this->mpi_now,           this->mpi_bolus_history.clone(),
          this->mpi_activity,      this->mpi_use_sensor_margin,
          this->mpi_fault.clone(), this->mpi_weight_kg};
    }
  };

  static uint64_t mmol_tenths_to_mg_dL(uint64_t mmol_tenths);
  static PrecisionInput convert_mmol_input(const MmolPrecisionInput &input);
  static PrecisionResult validated_mmol_bolus(const MmolPrecisionInput &input,
                                              const PrecisionParams &params);
  enum class RoundingMode { ROUNDTWENTIETH, ROUNDTENTH, ROUNDHALF, ROUNDUNIT };

  template <typename T1>
  static T1 RoundingMode_rect(T1 f, T1 f0, T1 f1, T1 f2, RoundingMode r) {
    switch (r) {
    case RoundingMode::ROUNDTWENTIETH: {
      return f;
    }
    case RoundingMode::ROUNDTENTH: {
      return f0;
    }
    case RoundingMode::ROUNDHALF: {
      return f1;
    }
    case RoundingMode::ROUNDUNIT: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 RoundingMode_rec(T1 f, T1 f0, T1 f1, T1 f2, RoundingMode r) {
    switch (r) {
    case RoundingMode::ROUNDTWENTIETH: {
      return f;
    }
    case RoundingMode::ROUNDTENTH: {
      return f0;
    }
    case RoundingMode::ROUNDHALF: {
      return f1;
    }
    case RoundingMode::ROUNDUNIT: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  static uint64_t round_down_to_increment(uint64_t t, uint64_t increment);
  static Insulin_twentieth apply_rounding(RoundingMode mode, uint64_t t);
  static std::optional<Insulin_twentieth>
  final_delivery(RoundingMode mode, const PrecisionResult &result);

  struct PumpState {
    uint64_t ps_reservoir_twentieths;
    uint64_t ps_basal_rate_hundredths;
    Minutes ps_last_bolus_time;
    bool ps_occlusion_detected;
    uint64_t ps_battery_percent;

    // ACCESSORS
    PumpState clone() const {
      return PumpState{this->ps_reservoir_twentieths,
                       this->ps_basal_rate_hundredths, this->ps_last_bolus_time,
                       this->ps_occlusion_detected, this->ps_battery_percent};
    }
  };

  static bool pump_can_deliver(const PumpState &state, uint64_t dose);
  static uint64_t reservoir_after_bolus(const PumpState &state, uint64_t dose);
  static uint64_t option_nat_default(const std::optional<uint64_t> &x,
                                     uint64_t d);
  static bool pump_accepts_result(const PumpState &pump, RoundingMode mode,
                                  const PrecisionResult &r);
  static uint64_t pump_reservoir_after_result(const PumpState &pump,
                                              RoundingMode mode,
                                              const PrecisionResult &r);
  static inline const PrecisionParams witness_prec_params =
      PrecisionParams{UINT64_C(100), UINT64_C(500), Mg_dL{UINT64_C(100)},
                      UINT64_C(240), InsulinType::INSULIN_HUMALOG};
  static inline const PrecisionInput standard_input = PrecisionInput{
      Grams{UINT64_C(60)},       Mg_dL{UINT64_C(150)},           UINT64_C(0),
      List<BolusEvent>::nil(),   ActivityState::ACTIVITY_NORMAL, false,
      FaultStatus::fault_none(), std::optional<uint64_t>()};
  static inline const MmolPrecisionInput mmol_input =
      MmolPrecisionInput{Grams{UINT64_C(60)},
                         UINT64_C(83),
                         UINT64_C(0),
                         List<BolusEvent>::nil(),
                         ActivityState::ACTIVITY_NORMAL,
                         false,
                         FaultStatus::fault_none(),
                         std::optional<uint64_t>()};
  static inline const PrecisionInput high_iob_input = PrecisionInput{
      Grams{UINT64_C(0)},
      Mg_dL{UINT64_C(150)},
      UINT64_C(100),
      List<BolusEvent>::cons(
          BolusEvent{UINT64_C(120), UINT64_C(85)},
          List<BolusEvent>::cons(BolusEvent{UINT64_C(100), UINT64_C(80)},
                                 List<BolusEvent>::nil())),
      ActivityState::ACTIVITY_NORMAL,
      false,
      FaultStatus::fault_none(),
      std::optional<uint64_t>()};
  static inline const PrecisionInput tdd_exceeded_input = PrecisionInput{
      Grams{UINT64_C(60)},
      Mg_dL{UINT64_C(150)},
      UINT64_C(2000),
      List<BolusEvent>::cons(
          BolusEvent{UINT64_C(500), UINT64_C(1800)},
          List<BolusEvent>::cons(
              BolusEvent{UINT64_C(500), UINT64_C(1500)},
              List<BolusEvent>::cons(BolusEvent{UINT64_C(500), UINT64_C(1000)},
                                     List<BolusEvent>::nil()))),
      ActivityState::ACTIVITY_NORMAL,
      false,
      FaultStatus::fault_none(),
      std::make_optional<uint64_t>(UINT64_C(70))};
  static inline const PrecisionInput occlusion_input = PrecisionInput{
      Grams{UINT64_C(60)},
      Mg_dL{UINT64_C(150)},
      UINT64_C(120),
      List<BolusEvent>::cons(BolusEvent{UINT64_C(40), UINT64_C(100)},
                             List<BolusEvent>::nil()),
      ActivityState::ACTIVITY_NORMAL,
      false,
      FaultStatus::fault_occlusion(),
      std::optional<uint64_t>()};
  static inline const PrecisionInput battery_low_input = PrecisionInput{
      Grams{UINT64_C(60)},
      Mg_dL{UINT64_C(150)},
      UINT64_C(120),
      List<BolusEvent>::cons(BolusEvent{UINT64_C(40), UINT64_C(100)},
                             List<BolusEvent>::nil()),
      ActivityState::ACTIVITY_NORMAL,
      false,
      FaultStatus::fault_batterylow(),
      std::optional<uint64_t>()};
  static inline const PrecisionInput pediatric_capped_input =
      PrecisionInput{Grams{UINT64_C(200)},
                     Mg_dL{UINT64_C(400)},
                     UINT64_C(0),
                     List<BolusEvent>::nil(),
                     ActivityState::ACTIVITY_NORMAL,
                     false,
                     FaultStatus::fault_none(),
                     std::make_optional<uint64_t>(UINT64_C(20))};
  static inline const PumpState standard_pump = PumpState{
      UINT64_C(2000), UINT64_C(100), UINT64_C(0), false, UINT64_C(80)};
  static inline const PumpState low_battery_pump =
      PumpState{UINT64_C(2000), UINT64_C(100), UINT64_C(0), false, UINT64_C(4)};
  static inline const PrecisionResult standard_result =
      validated_precision_bolus(standard_input, witness_prec_params);
  static inline const PrecisionResult mmol_result =
      validated_mmol_bolus(mmol_input, witness_prec_params);
  static inline const PrecisionResult battery_low_result =
      validated_precision_bolus(battery_low_input, witness_prec_params);
  static inline const PrecisionResult pediatric_result =
      validated_precision_bolus(pediatric_capped_input, witness_prec_params);
  static inline const uint64_t standard_result_code =
      standard_result.precision_result_code();
  static inline const bool standard_modified =
      standard_result.result_modified();
  static inline const uint64_t standard_final_delivery_half =
      option_nat_default(
          final_delivery(RoundingMode::ROUNDHALF, standard_result),
          UINT64_C(0));
  static inline const bool standard_pump_accepts = pump_accepts_result(
      standard_pump, RoundingMode::ROUNDHALF, standard_result);
  static inline const uint64_t standard_reservoir_after =
      pump_reservoir_after_result(standard_pump, RoundingMode::ROUNDHALF,
                                  standard_result);
  static inline const uint64_t mmol_result_code =
      mmol_result.precision_result_code();
  static inline const uint64_t mmol_final_delivery_tenth = option_nat_default(
      final_delivery(RoundingMode::ROUNDTENTH, mmol_result), UINT64_C(0));
  static inline const uint64_t high_iob_error_code =
      validated_precision_bolus(high_iob_input, witness_prec_params)
          .precision_result_code();
  static inline const uint64_t tdd_error_code =
      validated_precision_bolus(tdd_exceeded_input, witness_prec_params)
          .precision_result_code();
  static inline const uint64_t occlusion_error_code =
      validated_precision_bolus(occlusion_input, witness_prec_params)
          .precision_result_code();
  static inline const uint64_t battery_low_result_code =
      battery_low_result.precision_result_code();
  static inline const bool battery_low_pump_denied = !(pump_accepts_result(
      low_battery_pump, RoundingMode::ROUNDHALF, battery_low_result));
  static inline const uint64_t pediatric_result_code =
      pediatric_result.precision_result_code();
  static inline const bool pediatric_modified =
      pediatric_result.result_modified();
  static inline const uint64_t pediatric_final_delivery = option_nat_default(
      final_delivery(RoundingMode::ROUNDTWENTIETH, pediatric_result),
      UINT64_C(0));
  static inline const bool low_reservoir_blocks =
      FaultStatus::fault_lowreservoir(UINT64_C(5)).fault_blocks_bolus();
  static inline const bool unknown_fault_blocks =
      FaultStatus::fault_unknown().fault_blocks_bolus();
};

#endif // INCLUDED_VALIDATED_PUMP_DELIVERY_TRACE
