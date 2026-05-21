#ifndef INCLUDED_VALIDATED_VIRTUAL_CROSSMATCH_TRACE
#define INCLUDED_VALIDATED_VIRTUAL_CROSSMATCH_TRACE

#include <algorithm>
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
  bool existsb(F0 &&f) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return false;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return (f(a0) || a1->existsb(f));
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

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<List<T1>, F0 &, A &>
  List<T1> flat_map(F0 &&f) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return List<T1>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return f(a0).app(a1->template flat_map<T1>(f));
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

  List<A> app(List<A> m) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return m;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return List<A>::cons(a0, a1->app(std::move(m)));
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

struct PeanoNat {
  static bool eq_dec(uint64_t n, uint64_t m);
};

struct Bool {
  static bool bool_dec(bool b1, bool b2);
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

struct ValidatedVirtualCrossmatchTraceCase {
  enum class HLALocus { LOCUS_A, LOCUS_B, LOCUS_DR };

  template <typename T1>
  static T1 HLALocus_rect(T1 f, T1 f0, T1 f1, HLALocus h) {
    switch (h) {
    case HLALocus::LOCUS_A: {
      return f;
    }
    case HLALocus::LOCUS_B: {
      return f0;
    }
    case HLALocus::LOCUS_DR: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 HLALocus_rec(T1 f, T1 f0, T1 f1, HLALocus h) {
    switch (h) {
    case HLALocus::LOCUS_A: {
      return f;
    }
    case HLALocus::LOCUS_B: {
      return f0;
    }
    case HLALocus::LOCUS_DR: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  static bool hla_locus_eq_dec(HLALocus x, HLALocus y);

  struct HLAAllele {
    HLALocus hla_locus;
    uint64_t hla_group;

    // ACCESSORS
    HLAAllele clone() const {
      return HLAAllele{this->hla_locus, this->hla_group};
    }
  };

  static bool hla_allele_eq_dec(const HLAAllele &x, const HLAAllele &y);
  static bool hla_allele_eqb(const HLAAllele &x, const HLAAllele &y);

  struct HLATyping {
    List<HLAAllele> hla_typed_alleles;

    // ACCESSORS
    HLATyping clone() const {
      return HLATyping{this->hla_typed_alleles.clone()};
    }
  };

  struct HLAEpitope {
    uint64_t epitope_id;
    HLALocus epitope_locus;
    bool epitope_immunogenic;

    // ACCESSORS
    HLAEpitope clone() const {
      return HLAEpitope{this->epitope_id, this->epitope_locus,
                        this->epitope_immunogenic};
    }
  };

  static bool epitope_eq_dec(const HLAEpitope &x, const HLAEpitope &y);
  static bool epitope_eqb(const HLAEpitope &x, const HLAEpitope &y);
  static inline const HLAEpitope eplet_62GE =
      HLAEpitope{UINT64_C(62), HLALocus::LOCUS_A, true};
  static inline const HLAEpitope eplet_65QIA =
      HLAEpitope{UINT64_C(65), HLALocus::LOCUS_A, true};
  static inline const HLAEpitope eplet_142T =
      HLAEpitope{UINT64_C(142), HLALocus::LOCUS_B, true};
  static inline const HLAEpitope eplet_77N =
      HLAEpitope{UINT64_C(77), HLALocus::LOCUS_DR, true};
  static List<HLAEpitope> allele_epitopes(const HLAAllele &a);
  static List<HLAEpitope> typing_epitopes(const HLATyping &t);
  static List<HLAEpitope> epitope_dedup(const List<HLAEpitope> &l);

  struct EpitopeAntibody {
    HLAEpitope ab_epitope;
    uint64_t ab_mfi;
    bool ab_complement_fixing;

    // ACCESSORS
    EpitopeAntibody clone() const {
      return EpitopeAntibody{this->ab_epitope.clone(), this->ab_mfi,
                             this->ab_complement_fixing};
    }
  };

  struct VirtualXMProfile {
    List<EpitopeAntibody> vxm_epitope_abs;
    uint64_t vxm_current_pra;
    uint64_t vxm_peak_pra;
    uint64_t vxm_sensitization_events;

    // ACCESSORS
    VirtualXMProfile clone() const {
      return VirtualXMProfile{this->vxm_epitope_abs.clone(),
                              this->vxm_current_pra, this->vxm_peak_pra,
                              this->vxm_sensitization_events};
    }
  };

  struct MFIThresholdConfig {
    uint64_t mfi_cfg_negative;
    uint64_t mfi_cfg_weak_positive;
    uint64_t mfi_cfg_moderate;
    uint64_t mfi_cfg_strong;
    uint64_t mfi_cfg_lab_id;
    bool mfi_cfg_validated;

    // ACCESSORS
    MFIThresholdConfig clone() const {
      return MFIThresholdConfig{
          this->mfi_cfg_negative, this->mfi_cfg_weak_positive,
          this->mfi_cfg_moderate, this->mfi_cfg_strong,
          this->mfi_cfg_lab_id,   this->mfi_cfg_validated};
    }
  };

  static bool mfi_config_valid(const MFIThresholdConfig &cfg);
  static inline const MFIThresholdConfig example_luminex_thresholds =
      MFIThresholdConfig{UINT64_C(1000),  UINT64_C(3000), UINT64_C(8000),
                         UINT64_C(12000), UINT64_C(1),    true};

  struct ValidatedMFIConfig {
    MFIThresholdConfig vmc_config;

    // ACCESSORS
    ValidatedMFIConfig clone() const {
      return ValidatedMFIConfig{this->vmc_config.clone()};
    }
  };

  static inline const ValidatedMFIConfig validated_luminex =
      ValidatedMFIConfig{example_luminex_thresholds};
  enum class MFIStrength {
    MFI_NEGATIVE,
    MFI_WEAKPOSITIVE,
    MFI_MODERATE,
    MFI_STRONG,
    MFI_VERYSTRONG
  };

  template <typename T1>
  static T1 MFIStrength_rect(T1 f, T1 f0, T1 f1, T1 f2, T1 f3, MFIStrength m) {
    switch (m) {
    case MFIStrength::MFI_NEGATIVE: {
      return f;
    }
    case MFIStrength::MFI_WEAKPOSITIVE: {
      return f0;
    }
    case MFIStrength::MFI_MODERATE: {
      return f1;
    }
    case MFIStrength::MFI_STRONG: {
      return f2;
    }
    case MFIStrength::MFI_VERYSTRONG: {
      return f3;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 MFIStrength_rec(T1 f, T1 f0, T1 f1, T1 f2, T1 f3, MFIStrength m) {
    switch (m) {
    case MFIStrength::MFI_NEGATIVE: {
      return f;
    }
    case MFIStrength::MFI_WEAKPOSITIVE: {
      return f0;
    }
    case MFIStrength::MFI_MODERATE: {
      return f1;
    }
    case MFIStrength::MFI_STRONG: {
      return f2;
    }
    case MFIStrength::MFI_VERYSTRONG: {
      return f3;
    }
    default:
      std::unreachable();
    }
  }

  static MFIStrength classify_mfi_with_config(const MFIThresholdConfig &cfg,
                                              uint64_t mfi);
  static MFIStrength classify_mfi_safe(const ValidatedMFIConfig &vcfg,
                                       uint64_t mfi);
  static inline const uint64_t mfi_negative_threshold = UINT64_C(1000);
  static uint64_t max_dsa_mfi(const VirtualXMProfile &recipient,
                              const HLATyping &donor);
  static bool has_complement_fixing_dsa(const VirtualXMProfile &recipient,
                                        const HLATyping &donor);
  enum class VirtualXMResult {
    VXM_NEGATIVE,
    VXM_WEAKPOSITIVE,
    VXM_POSITIVE,
    VXM_STRONGPOSITIVE
  };

  template <typename T1>
  static T1 VirtualXMResult_rect(T1 f, T1 f0, T1 f1, T1 f2, VirtualXMResult v) {
    switch (v) {
    case VirtualXMResult::VXM_NEGATIVE: {
      return f;
    }
    case VirtualXMResult::VXM_WEAKPOSITIVE: {
      return f0;
    }
    case VirtualXMResult::VXM_POSITIVE: {
      return f1;
    }
    case VirtualXMResult::VXM_STRONGPOSITIVE: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 VirtualXMResult_rec(T1 f, T1 f0, T1 f1, T1 f2, VirtualXMResult v) {
    switch (v) {
    case VirtualXMResult::VXM_NEGATIVE: {
      return f;
    }
    case VirtualXMResult::VXM_WEAKPOSITIVE: {
      return f0;
    }
    case VirtualXMResult::VXM_POSITIVE: {
      return f1;
    }
    case VirtualXMResult::VXM_STRONGPOSITIVE: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  static VirtualXMResult
  virtual_crossmatch_safe(const ValidatedMFIConfig &vcfg,
                          const VirtualXMProfile &recipient,
                          const HLATyping &donor);
  enum class TransplantAcceptability {
    ACCEPTABLE,
    ACCEPTABLE_WITH_DESENSITIZATION,
    UNACCEPTABLE_HIGH_RISK,
    ABSOLUTE_CONTRAINDICATION
  };

  template <typename T1>
  static T1 TransplantAcceptability_rect(T1 f, T1 f0, T1 f1, T1 f2,
                                         TransplantAcceptability t) {
    switch (t) {
    case TransplantAcceptability::ACCEPTABLE: {
      return f;
    }
    case TransplantAcceptability::ACCEPTABLE_WITH_DESENSITIZATION: {
      return f0;
    }
    case TransplantAcceptability::UNACCEPTABLE_HIGH_RISK: {
      return f1;
    }
    case TransplantAcceptability::ABSOLUTE_CONTRAINDICATION: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 TransplantAcceptability_rec(T1 f, T1 f0, T1 f1, T1 f2,
                                        TransplantAcceptability t) {
    switch (t) {
    case TransplantAcceptability::ACCEPTABLE: {
      return f;
    }
    case TransplantAcceptability::ACCEPTABLE_WITH_DESENSITIZATION: {
      return f0;
    }
    case TransplantAcceptability::UNACCEPTABLE_HIGH_RISK: {
      return f1;
    }
    case TransplantAcceptability::ABSOLUTE_CONTRAINDICATION: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  static TransplantAcceptability
  transplant_acceptability(VirtualXMResult vxm, bool complement_fixing_dsa);
  static TransplantAcceptability
  full_virtual_crossmatch_safe(const ValidatedMFIConfig &vcfg,
                               const VirtualXMProfile &recipient,
                               const HLATyping &donor);
  enum class TestConfidence {
    CONFIDENCE_HIGH,
    CONFIDENCE_MEDIUM,
    CONFIDENCE_LOW
  };

  template <typename T1>
  static T1 TestConfidence_rect(T1 f, T1 f0, T1 f1, TestConfidence t) {
    switch (t) {
    case TestConfidence::CONFIDENCE_HIGH: {
      return f;
    }
    case TestConfidence::CONFIDENCE_MEDIUM: {
      return f0;
    }
    case TestConfidence::CONFIDENCE_LOW: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 TestConfidence_rec(T1 f, T1 f0, T1 f1, TestConfidence t) {
    switch (t) {
    case TestConfidence::CONFIDENCE_HIGH: {
      return f;
    }
    case TestConfidence::CONFIDENCE_MEDIUM: {
      return f0;
    }
    case TestConfidence::CONFIDENCE_LOW: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }
  enum class CrossmatchResult {
    XM_COMPATIBLE,
    XM_INCOMPATIBLE,
    XM_INCONCLUSIVE,
    XM_NOT_DONE
  };

  template <typename T1>
  static T1 CrossmatchResult_rect(T1 f, T1 f0, T1 f1, T1 f2,
                                  CrossmatchResult c) {
    switch (c) {
    case CrossmatchResult::XM_COMPATIBLE: {
      return f;
    }
    case CrossmatchResult::XM_INCOMPATIBLE: {
      return f0;
    }
    case CrossmatchResult::XM_INCONCLUSIVE: {
      return f1;
    }
    case CrossmatchResult::XM_NOT_DONE: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 CrossmatchResult_rec(T1 f, T1 f0, T1 f1, T1 f2,
                                 CrossmatchResult c) {
    switch (c) {
    case CrossmatchResult::XM_COMPATIBLE: {
      return f;
    }
    case CrossmatchResult::XM_INCOMPATIBLE: {
      return f0;
    }
    case CrossmatchResult::XM_INCONCLUSIVE: {
      return f1;
    }
    case CrossmatchResult::XM_NOT_DONE: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  struct CrossmatchWithUncertainty {
    CrossmatchResult xmu_result;
    uint64_t xmu_method;
    TestConfidence xmu_confidence;

    // ACCESSORS
    CrossmatchWithUncertainty clone() const {
      return CrossmatchWithUncertainty{this->xmu_result, this->xmu_method,
                                       this->xmu_confidence};
    }
  };

  static bool safe_to_release(const CrossmatchWithUncertainty &xm);

  struct SafeTransfusionOrder {
    uint64_t sto_recipient_id;
    uint64_t sto_product_id;
    bool sto_compatibility_check;
    CrossmatchWithUncertainty sto_crossmatch;
    uint64_t sto_sample_collection_time;
    uint64_t sto_authorized_by;
    bool sto_emergency_release;

    // ACCESSORS
    SafeTransfusionOrder clone() const {
      return SafeTransfusionOrder{
          this->sto_recipient_id,           this->sto_product_id,
          this->sto_compatibility_check,    this->sto_crossmatch.clone(),
          this->sto_sample_collection_time, this->sto_authorized_by,
          this->sto_emergency_release};
    }
  };

  static bool order_sample_valid(uint64_t collection_time,
                                 uint64_t current_time);
  static bool transfusion_order_authorized(const SafeTransfusionOrder &order,
                                           uint64_t current_time);
  static std::optional<SafeTransfusionOrder> create_safe_transfusion_order(
      uint64_t recipient_id, uint64_t product_id, bool compat_result,
      CrossmatchWithUncertainty xm, uint64_t sample_time, uint64_t current_time,
      uint64_t authorizer, bool is_emergency);
  static inline const HLATyping donor_hla = HLATyping{List<HLAAllele>::cons(
      HLAAllele{HLALocus::LOCUS_A, UINT64_C(2)},
      List<HLAAllele>::cons(
          HLAAllele{HLALocus::LOCUS_A, UINT64_C(3)},
          List<HLAAllele>::cons(
              HLAAllele{HLALocus::LOCUS_B, UINT64_C(7)},
              List<HLAAllele>::cons(HLAAllele{HLALocus::LOCUS_DR, UINT64_C(4)},
                                    List<HLAAllele>::nil()))))};
  static inline const VirtualXMProfile weak_profile =
      VirtualXMProfile{List<EpitopeAntibody>::cons(
                           EpitopeAntibody{eplet_65QIA, UINT64_C(2500), false},
                           List<EpitopeAntibody>::cons(
                               EpitopeAntibody{eplet_77N, UINT64_C(800), false},
                               List<EpitopeAntibody>::nil())),
                       UINT64_C(32), UINT64_C(40), UINT64_C(2)};
  static inline const VirtualXMProfile strong_profile = VirtualXMProfile{
      List<EpitopeAntibody>::cons(
          EpitopeAntibody{eplet_65QIA, UINT64_C(9000), true},
          List<EpitopeAntibody>::cons(
              EpitopeAntibody{eplet_142T, UINT64_C(6000), false},
              List<EpitopeAntibody>::nil())),
      UINT64_C(95), UINT64_C(98), UINT64_C(5)};
  static inline const CrossmatchWithUncertainty good_crossmatch =
      CrossmatchWithUncertainty{CrossmatchResult::XM_COMPATIBLE, UINT64_C(1),
                                TestConfidence::CONFIDENCE_HIGH};
  static inline const CrossmatchWithUncertainty bad_crossmatch =
      CrossmatchWithUncertainty{CrossmatchResult::XM_INCOMPATIBLE, UINT64_C(1),
                                TestConfidence::CONFIDENCE_HIGH};
  static bool risk_acceptable(TransplantAcceptability a);
  static inline const bool sample_virtual_zero_negative = []() {
    switch (classify_mfi_safe(validated_luminex, UINT64_C(0))) {
    case MFIStrength::MFI_NEGATIVE: {
      return true;
    }
    default: {
      return false;
    }
    }
  }();
  static inline const uint64_t sample_dedup_count =
      epitope_dedup(typing_epitopes(donor_hla)).length();
  static inline const bool sample_weak_acceptability = []() {
    switch (full_virtual_crossmatch_safe(validated_luminex, weak_profile,
                                         donor_hla)) {
    case TransplantAcceptability::ACCEPTABLE_WITH_DESENSITIZATION: {
      return true;
    }
    default: {
      return false;
    }
    }
  }();
  static inline const bool sample_strong_absolute_contra = []() {
    switch (full_virtual_crossmatch_safe(validated_luminex, strong_profile,
                                         donor_hla)) {
    case TransplantAcceptability::ABSOLUTE_CONTRAINDICATION: {
      return true;
    }
    default: {
      return false;
    }
    }
  }();
  static inline const bool sample_strong_has_complement_fixing_dsa =
      has_complement_fixing_dsa(strong_profile, donor_hla);
  static inline const uint64_t sample_strong_max_mfi =
      max_dsa_mfi(strong_profile, donor_hla);
  static inline const uint64_t sample_lab_id =
      validated_luminex.vmc_config.mfi_cfg_lab_id;
  static inline const bool sample_order_created = []() -> bool {
    auto _cs = create_safe_transfusion_order(
        UINT64_C(100), UINT64_C(200),
        risk_acceptable(full_virtual_crossmatch_safe(validated_luminex,
                                                     weak_profile, donor_hla)),
        good_crossmatch, UINT64_C(0), UINT64_C(1000), UINT64_C(77), false);
    if (_cs.has_value()) {
      const SafeTransfusionOrder &_x = *_cs;
      return true;
    } else {
      return false;
    }
  }();
  static inline const bool sample_order_blocked = []() -> bool {
    auto _cs = create_safe_transfusion_order(
        UINT64_C(100), UINT64_C(201),
        risk_acceptable(full_virtual_crossmatch_safe(
            validated_luminex, strong_profile, donor_hla)),
        bad_crossmatch, UINT64_C(0), UINT64_C(1000), UINT64_C(77), false);
    if (_cs.has_value()) {
      const SafeTransfusionOrder &_x = *_cs;
      return false;
    } else {
      return true;
    }
  }();
  static inline const bool sample_authorized_order_stays_authorized =
      []() -> bool {
    auto _cs = create_safe_transfusion_order(
        UINT64_C(100), UINT64_C(202), true, good_crossmatch, UINT64_C(100),
        UINT64_C(200), UINT64_C(88), false);
    if (_cs.has_value()) {
      const SafeTransfusionOrder &order = *_cs;
      return transfusion_order_authorized(order, UINT64_C(200));
    } else {
      return false;
    }
  }();
};

#endif // INCLUDED_VALIDATED_VIRTUAL_CROSSMATCH_TRACE
