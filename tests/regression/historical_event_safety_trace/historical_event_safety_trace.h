#ifndef INCLUDED_HISTORICAL_EVENT_SAFETY_TRACE
#define INCLUDED_HISTORICAL_EVENT_SAFETY_TRACE

#include <algorithm>
#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  List clone() const {
    List _out{};

    struct _CloneFrame {
      const List *_src;
      List *_dst;
    };

    std::vector<_CloneFrame> _stack;
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List *_src = _frame._src;
      List *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        const auto &_alt = std::get<Nil>(_src->v());
        _dst->d_v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->d_v_ =
            Cons{_alt.d_a0, _alt.d_a1 ? std::make_unique<List>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->d_v_);
        if (_alt.d_a1)
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  static List<t_A> nil() { return List(Nil{}); }

  static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons{std::move(a0), std::make_unique<List<t_A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List>> _stack;
    auto _drain = [&](List &_node) {
      if (std::holds_alternative<Cons>(_node.d_v_)) {
        auto &_alt = std::get<Cons>(_node.d_v_);
        if (_alt.d_a1)
          _stack.push_back(std::move(_alt.d_a1));
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

  unsigned int length() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return ((*(d_a1)).length() + 1);
    }
  }
};

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

struct HistoricalEventSafetyTraceCase {
  struct State {
    unsigned int reservoir_level_cm;
    unsigned int downstream_stage_cm;
    unsigned int gate_open_pct;

    // ACCESSORS
    State clone() const {
      return State{(*(this)).reservoir_level_cm, (*(this)).downstream_stage_cm,
                   (*(this)).gate_open_pct};
    }
  };

  struct PlantConfig {
    unsigned int max_reservoir_cm;
    unsigned int max_downstream_cm;
    unsigned int gate_capacity_cm;
    unsigned int forecast_error_pct;
    unsigned int gate_slew_pct;
    unsigned int max_stage_rise_cm;
    unsigned int reservoir_area_min_cm2;
    unsigned int reservoir_area_max_cm2;
    std::function<unsigned int(unsigned int)> reservoir_area_curve_cm2;
    unsigned int design_head_cm;
    unsigned int timestep_s;

    // ACCESSORS
    PlantConfig clone() const {
      return PlantConfig{(*(this)).max_reservoir_cm,
                         (*(this)).max_downstream_cm,
                         (*(this)).gate_capacity_cm,
                         (*(this)).forecast_error_pct,
                         (*(this)).gate_slew_pct,
                         (*(this)).max_stage_rise_cm,
                         (*(this)).reservoir_area_min_cm2,
                         (*(this)).reservoir_area_max_cm2,
                         (*(this)).reservoir_area_curve_cm2,
                         (*(this)).design_head_cm,
                         (*(this)).timestep_s};
    }
  };

  static bool is_safe_bool(const PlantConfig &pconf, const State &s);

  struct InflowRecord {
    unsigned int ir_timestep;
    unsigned int ir_inflow_cm;

    // ACCESSORS
    InflowRecord clone() const {
      return InflowRecord{(*(this)).ir_timestep, (*(this)).ir_inflow_cm};
    }
  };

  using HistoricalEvent = List<InflowRecord>;
  static unsigned int event_to_inflow(const List<InflowRecord> &event,
                                      unsigned int default_inflow,
                                      const unsigned int &t);

  struct TestResult {
    unsigned int tr_event_name;
    bool tr_initial_safe;
    bool tr_final_safe;
    unsigned int tr_max_level;
    unsigned int tr_max_stage;

    // ACCESSORS
    TestResult clone() const {
      return TestResult{(*(this)).tr_event_name, (*(this)).tr_initial_safe,
                        (*(this)).tr_final_safe, (*(this)).tr_max_level,
                        (*(this)).tr_max_stage};
    }
  };

  template <MapsTo<unsigned int, unsigned int> F0,
            MapsTo<unsigned int, State, unsigned int> F1,
            MapsTo<unsigned int, unsigned int> F2>
  static State step_hist(F0 &&inflow, F1 &&ctrl, F2 &&stage_fn,
                         const PlantConfig &pconf, const State &s,
                         const unsigned int &t) {
    unsigned int out =
        std::min((100u ? (pconf.gate_capacity_cm * ctrl(s, t)) / 100u : 0),
                 (s.reservoir_level_cm + inflow(t)));
    unsigned int new_level =
        ((((s.reservoir_level_cm + inflow(t)) - out) >
                  (s.reservoir_level_cm + inflow(t))
              ? 0
              : ((s.reservoir_level_cm + inflow(t)) - out)));
    unsigned int new_stage = stage_fn(out);
    return State{new_level, new_stage, ctrl(s, t)};
  }

  template <MapsTo<unsigned int, unsigned int> F0,
            MapsTo<unsigned int, State, unsigned int> F1,
            MapsTo<unsigned int, unsigned int> F2>
  static std::pair<std::pair<State, unsigned int>, unsigned int>
  simulate_with_max(F0 &&inflow, F1 &&ctrl, F2 &&stage_fn,
                    const PlantConfig &pconf, const unsigned int &horizon,
                    State s, unsigned int max_level, unsigned int max_stage) {
    if (horizon <= 0) {
      return std::make_pair(std::make_pair(std::move(s), max_level), max_stage);
    } else {
      unsigned int k = horizon - 1;
      State s_ = step_hist(inflow, ctrl, stage_fn, pconf, std::move(s), k);
      return simulate_with_max(inflow, ctrl, stage_fn, pconf, k, s_,
                               std::max(max_level, s_.reservoir_level_cm),
                               std::max(max_stage, s_.downstream_stage_cm));
    }
  }

  template <MapsTo<unsigned int, State, unsigned int> F3,
            MapsTo<unsigned int, unsigned int> F4>
  static TestResult
  run_historical_test(const PlantConfig &pconf, List<InflowRecord> event,
                      unsigned int default_inflow, F3 &&ctrl, F4 &&stage_fn,
                      const State &initial_state, const unsigned int &horizon,
                      unsigned int event_id) {
    std::function<unsigned int(unsigned int)> inflow =
        [=](unsigned int _x0) mutable -> unsigned int {
      return event_to_inflow(event, default_inflow, _x0);
    };
    bool initial_safe = is_safe_bool(pconf, initial_state);
    auto _cs = simulate_with_max(inflow, ctrl, stage_fn, pconf, horizon,
                                 initial_state, 0u, 0u);
    const std::pair<State, unsigned int> &p = _cs.first;
    const unsigned int &max_stg = _cs.second;
    const State &final_state = p.first;
    const unsigned int &max_lev = p.second;
    bool final_safe = is_safe_bool(pconf, final_state);
    return TestResult{event_id, initial_safe, final_safe, max_lev, max_stg};
  }

  static bool test_passes(const TestResult &result);
  static bool all_tests_pass(const List<TestResult> &results);
  using RatingTable = List<std::pair<unsigned int, unsigned int>>;
  static unsigned int
  stage_from_table(const List<std::pair<unsigned int, unsigned int>> &tbl,
                   unsigned int base_stage, const unsigned int &out);

  struct MonotoneRatingTable {
    RatingTable mrt_table;

    // ACCESSORS
    MonotoneRatingTable clone() const {
      return MonotoneRatingTable{(*(this)).mrt_table};
    }
  };

  static inline const HistoricalEvent flood_1983_inflows =
      List<InflowRecord>::cons(
          InflowRecord{0u, 50u},
          List<InflowRecord>::cons(
              InflowRecord{1u, 75u},
              List<InflowRecord>::cons(
                  InflowRecord{2u, 100u},
                  List<InflowRecord>::cons(
                      InflowRecord{3u, 150u},
                      List<InflowRecord>::cons(
                          InflowRecord{4u, 200u},
                          List<InflowRecord>::cons(
                              InflowRecord{5u, 250u},
                              List<InflowRecord>::cons(
                                  InflowRecord{6u, 300u},
                                  List<InflowRecord>::cons(
                                      InflowRecord{7u, 250u},
                                      List<InflowRecord>::cons(
                                          InflowRecord{8u, 200u},
                                          List<InflowRecord>::cons(
                                              InflowRecord{9u, 150u},
                                              List<InflowRecord>::
                                                  nil()))))))))));
  static inline const HistoricalEvent flood_2011_inflows =
      List<InflowRecord>::cons(
          InflowRecord{0u, 100u},
          List<InflowRecord>::cons(
              InflowRecord{1u, 150u},
              List<InflowRecord>::cons(
                  InflowRecord{2u, 200u},
                  List<InflowRecord>::cons(
                      InflowRecord{3u, 300u},
                      List<InflowRecord>::cons(
                          InflowRecord{4u, 400u},
                          List<InflowRecord>::cons(
                              InflowRecord{5u, 350u},
                              List<InflowRecord>::cons(
                                  InflowRecord{6u, 300u},
                                  List<InflowRecord>::cons(
                                      InflowRecord{7u, 250u},
                                      List<InflowRecord>::cons(
                                          InflowRecord{8u, 200u},
                                          List<InflowRecord>::cons(
                                              InflowRecord{9u, 150u},
                                              List<InflowRecord>::
                                                  nil()))))))))));
  static inline const HistoricalEvent dual_peak_scenario =
      List<InflowRecord>::cons(
          InflowRecord{0u, 30u},
          List<InflowRecord>::cons(
              InflowRecord{1u, 60u},
              List<InflowRecord>::cons(
                  InflowRecord{2u, 120u},
                  List<InflowRecord>::cons(
                      InflowRecord{3u, 200u},
                      List<InflowRecord>::cons(
                          InflowRecord{4u, 300u},
                          List<InflowRecord>::cons(
                              InflowRecord{5u, 380u},
                              List<InflowRecord>::cons(
                                  InflowRecord{6u, 420u},
                                  List<InflowRecord>::cons(
                                      InflowRecord{7u, 400u},
                                      List<InflowRecord>::cons(
                                          InflowRecord{8u, 350u},
                                          List<InflowRecord>::cons(
                                              InflowRecord{9u, 280u},
                                              List<InflowRecord>::
                                                  nil()))))))))));
  static inline const PlantConfig hist_witness_plant =
      PlantConfig{500u, 500u, 500u,
                  1u,   5u,   10u,
                  100u, 100u, [](const unsigned int &) {
return 100u; },
                  100u, 1u};
  static unsigned int hist_witness_stage(const unsigned int &out);
  static unsigned int hist_witness_ctrl(const State &s, const unsigned int &_x);
  static inline const State hist_witness_initial = State{50u, 0u, 0u};
  static inline const TestResult hist_test_1983 = run_historical_test(
      hist_witness_plant, flood_1983_inflows, 0u, hist_witness_ctrl,
      hist_witness_stage, hist_witness_initial, 10u, 1983u);
  static inline const TestResult hist_test_2011 = run_historical_test(
      hist_witness_plant, flood_2011_inflows, 0u, hist_witness_ctrl,
      hist_witness_stage, hist_witness_initial, 10u, 2011u);
  static inline const PlantConfig hoover_dam_config =
      PlantConfig{2200u, 100u,  500u,
                  15u,   5u,    10u,
                  1000u, 1000u, [](const unsigned int &) {
return 1000u; },
                  200u,  60u};
  static inline const State hoover_initial_state = State{1500u, 20u, 0u};
  static unsigned int hoover_controller(const State &s, const unsigned int &_x);
  static inline const MonotoneRatingTable hoover_rating_table =
      MonotoneRatingTable{List<std::pair<unsigned int, unsigned int>>::cons(
          std::make_pair(100u, 30u),
          List<std::pair<unsigned int, unsigned int>>::cons(
              std::make_pair(200u, 45u),
              List<std::pair<unsigned int, unsigned int>>::cons(
                  std::make_pair(300u, 60u),
                  List<std::pair<unsigned int, unsigned int>>::cons(
                      std::make_pair(400u, 75u),
                      List<std::pair<unsigned int, unsigned int>>::cons(
                          std::make_pair(500u, 90u),
                          List<std::pair<unsigned int,
                                         unsigned int>>::nil())))))};
  static unsigned int hoover_stage_from_rating(const unsigned int &out);
  static inline const TestResult hoover_test = run_historical_test(
      hoover_dam_config, dual_peak_scenario, 0u, hoover_controller,
      hoover_stage_from_rating, hoover_initial_state, 10u, 9001u);

  struct HistoricalScenarioBundle {
    PlantConfig hsb_hist_plant;
    MonotoneRatingTable hsb_hist_table;
    State hsb_hist_initial;
    TestResult hsb_test_1983;
    TestResult hsb_test_2011;
    PlantConfig hsb_hoover_plant;
    TestResult hsb_hoover_test;

    // ACCESSORS
    HistoricalScenarioBundle clone() const {
      return HistoricalScenarioBundle{(*(this)).hsb_hist_plant.clone(),
                                      (*(this)).hsb_hist_table.clone(),
                                      (*(this)).hsb_hist_initial.clone(),
                                      (*(this)).hsb_test_1983.clone(),
                                      (*(this)).hsb_test_2011.clone(),
                                      (*(this)).hsb_hoover_plant.clone(),
                                      (*(this)).hsb_hoover_test.clone()};
    }
  };

  static inline const HistoricalScenarioBundle historical_bundle =
      HistoricalScenarioBundle{hist_witness_plant,   hoover_rating_table,
                               hist_witness_initial, hist_test_1983,
                               hist_test_2011,       hoover_dam_config,
                               hoover_test};
  static unsigned int historical_lookup_1983(const unsigned int &t);
  static unsigned int historical_lookup_2011(const unsigned int &t);
  static bool witness_test_initial_safe_at(const unsigned int &h);
  static unsigned int witness_test_peak_level_at(const unsigned int &h);
  static unsigned int hoover_controller_sample(unsigned int level);
  static unsigned int hoover_stage_sample(const unsigned int &_x0);
  static inline const unsigned int sample_bundle_test_count =
      List<TestResult>::cons(
          historical_bundle.hsb_test_1983,
          List<TestResult>::cons(
              historical_bundle.hsb_test_2011,
              List<TestResult>::cons(historical_bundle.hsb_hoover_test,
                                     List<TestResult>::nil())))
          .length();
  static inline const bool sample_bundle_initial_safe =
      historical_bundle.hsb_test_1983.tr_initial_safe;
  static inline const unsigned int sample_bundle_hist_2011_id =
      historical_bundle.hsb_test_2011.tr_event_name;
  static inline const bool sample_all_tests_pass =
      all_tests_pass(List<TestResult>::cons(
          historical_bundle.hsb_test_1983,
          List<TestResult>::cons(
              historical_bundle.hsb_test_2011,
              List<TestResult>::cons(historical_bundle.hsb_hoover_test,
                                     List<TestResult>::nil()))));
};

#endif // INCLUDED_HISTORICAL_EVENT_SAFETY_TRACE
