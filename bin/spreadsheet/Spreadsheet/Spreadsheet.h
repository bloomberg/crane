#ifndef INCLUDED_SPREADSHEET
#define INCLUDED_SPREADSHEET

#include <cstdint>
#include <memory>
#include <optional>
#include <persistent_array.h>
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
  List<t_A> clone() const {
    List<t_A> _out{};

    struct _CloneFrame {
      const List<t_A> *_src;
      List<t_A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<t_A> *_src = _frame._src;
      List<t_A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->d_v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->d_v_ = Cons{_alt.d_a0,
                          _alt.d_a1 ? std::make_unique<List<t_A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->d_v_);
        if (_alt.d_a1) {
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        }
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
    std::vector<std::unique_ptr<List<t_A>>> _stack{};
    auto _drain = [&](List<t_A> &_node) {
      if (std::holds_alternative<Cons>(_node.d_v_)) {
        auto &_alt = std::get<Cons>(_node.d_v_);
        if (_alt.d_a1) {
          _stack.push_back(std::move(_alt.d_a1));
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

  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }
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

    std::vector<_CloneFrame> _stack{};
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const Uint *_src = _frame._src;
      Uint *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->d_v_ = Nil{};
      } else if (std::holds_alternative<D0>(_src->v())) {
        const auto &_alt = std::get<D0>(_src->v());
        _dst->d_v_ = D0{_alt.d_a0 ? std::make_unique<Uint>() : nullptr};
        auto &_dst_alt = std::get<D0>(_dst->d_v_);
        if (_alt.d_a0) {
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
        }
      } else if (std::holds_alternative<D1>(_src->v())) {
        const auto &_alt = std::get<D1>(_src->v());
        _dst->d_v_ = D1{_alt.d_a0 ? std::make_unique<Uint>() : nullptr};
        auto &_dst_alt = std::get<D1>(_dst->d_v_);
        if (_alt.d_a0) {
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
        }
      } else if (std::holds_alternative<D2>(_src->v())) {
        const auto &_alt = std::get<D2>(_src->v());
        _dst->d_v_ = D2{_alt.d_a0 ? std::make_unique<Uint>() : nullptr};
        auto &_dst_alt = std::get<D2>(_dst->d_v_);
        if (_alt.d_a0) {
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
        }
      } else if (std::holds_alternative<D3>(_src->v())) {
        const auto &_alt = std::get<D3>(_src->v());
        _dst->d_v_ = D3{_alt.d_a0 ? std::make_unique<Uint>() : nullptr};
        auto &_dst_alt = std::get<D3>(_dst->d_v_);
        if (_alt.d_a0) {
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
        }
      } else if (std::holds_alternative<D4>(_src->v())) {
        const auto &_alt = std::get<D4>(_src->v());
        _dst->d_v_ = D4{_alt.d_a0 ? std::make_unique<Uint>() : nullptr};
        auto &_dst_alt = std::get<D4>(_dst->d_v_);
        if (_alt.d_a0) {
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
        }
      } else if (std::holds_alternative<D5>(_src->v())) {
        const auto &_alt = std::get<D5>(_src->v());
        _dst->d_v_ = D5{_alt.d_a0 ? std::make_unique<Uint>() : nullptr};
        auto &_dst_alt = std::get<D5>(_dst->d_v_);
        if (_alt.d_a0) {
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
        }
      } else if (std::holds_alternative<D6>(_src->v())) {
        const auto &_alt = std::get<D6>(_src->v());
        _dst->d_v_ = D6{_alt.d_a0 ? std::make_unique<Uint>() : nullptr};
        auto &_dst_alt = std::get<D6>(_dst->d_v_);
        if (_alt.d_a0) {
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
        }
      } else if (std::holds_alternative<D7>(_src->v())) {
        const auto &_alt = std::get<D7>(_src->v());
        _dst->d_v_ = D7{_alt.d_a0 ? std::make_unique<Uint>() : nullptr};
        auto &_dst_alt = std::get<D7>(_dst->d_v_);
        if (_alt.d_a0) {
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
        }
      } else if (std::holds_alternative<D8>(_src->v())) {
        const auto &_alt = std::get<D8>(_src->v());
        _dst->d_v_ = D8{_alt.d_a0 ? std::make_unique<Uint>() : nullptr};
        auto &_dst_alt = std::get<D8>(_dst->d_v_);
        if (_alt.d_a0) {
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
        }
      } else {
        const auto &_alt = std::get<D9>(_src->v());
        _dst->d_v_ = D9{_alt.d_a0 ? std::make_unique<Uint>() : nullptr};
        auto &_dst_alt = std::get<D9>(_dst->d_v_);
        if (_alt.d_a0) {
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
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
    auto _drain = [&](Uint &_node) {
      if (std::holds_alternative<D0>(_node.d_v_)) {
        auto &_alt = std::get<D0>(_node.d_v_);
        if (_alt.d_a0) {
          _stack.push_back(std::move(_alt.d_a0));
        }
      }
      if (std::holds_alternative<D1>(_node.d_v_)) {
        auto &_alt = std::get<D1>(_node.d_v_);
        if (_alt.d_a0) {
          _stack.push_back(std::move(_alt.d_a0));
        }
      }
      if (std::holds_alternative<D2>(_node.d_v_)) {
        auto &_alt = std::get<D2>(_node.d_v_);
        if (_alt.d_a0) {
          _stack.push_back(std::move(_alt.d_a0));
        }
      }
      if (std::holds_alternative<D3>(_node.d_v_)) {
        auto &_alt = std::get<D3>(_node.d_v_);
        if (_alt.d_a0) {
          _stack.push_back(std::move(_alt.d_a0));
        }
      }
      if (std::holds_alternative<D4>(_node.d_v_)) {
        auto &_alt = std::get<D4>(_node.d_v_);
        if (_alt.d_a0) {
          _stack.push_back(std::move(_alt.d_a0));
        }
      }
      if (std::holds_alternative<D5>(_node.d_v_)) {
        auto &_alt = std::get<D5>(_node.d_v_);
        if (_alt.d_a0) {
          _stack.push_back(std::move(_alt.d_a0));
        }
      }
      if (std::holds_alternative<D6>(_node.d_v_)) {
        auto &_alt = std::get<D6>(_node.d_v_);
        if (_alt.d_a0) {
          _stack.push_back(std::move(_alt.d_a0));
        }
      }
      if (std::holds_alternative<D7>(_node.d_v_)) {
        auto &_alt = std::get<D7>(_node.d_v_);
        if (_alt.d_a0) {
          _stack.push_back(std::move(_alt.d_a0));
        }
      }
      if (std::holds_alternative<D8>(_node.d_v_)) {
        auto &_alt = std::get<D8>(_node.d_v_);
        if (_alt.d_a0) {
          _stack.push_back(std::move(_alt.d_a0));
        }
      }
      if (std::holds_alternative<D9>(_node.d_v_)) {
        auto &_alt = std::get<D9>(_node.d_v_);
        if (_alt.d_a0) {
          _stack.push_back(std::move(_alt.d_a0));
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

    std::vector<_CloneFrame> _stack{};
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const Uint0 *_src = _frame._src;
      Uint0 *_dst = _frame._dst;
      if (std::holds_alternative<Nil0>(_src->v())) {
        _dst->d_v_ = Nil0{};
      } else if (std::holds_alternative<D10>(_src->v())) {
        const auto &_alt = std::get<D10>(_src->v());
        _dst->d_v_ = D10{_alt.d_a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D10>(_dst->d_v_);
        if (_alt.d_a0) {
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
        }
      } else if (std::holds_alternative<D11>(_src->v())) {
        const auto &_alt = std::get<D11>(_src->v());
        _dst->d_v_ = D11{_alt.d_a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D11>(_dst->d_v_);
        if (_alt.d_a0) {
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
        }
      } else if (std::holds_alternative<D12>(_src->v())) {
        const auto &_alt = std::get<D12>(_src->v());
        _dst->d_v_ = D12{_alt.d_a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D12>(_dst->d_v_);
        if (_alt.d_a0) {
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
        }
      } else if (std::holds_alternative<D13>(_src->v())) {
        const auto &_alt = std::get<D13>(_src->v());
        _dst->d_v_ = D13{_alt.d_a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D13>(_dst->d_v_);
        if (_alt.d_a0) {
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
        }
      } else if (std::holds_alternative<D14>(_src->v())) {
        const auto &_alt = std::get<D14>(_src->v());
        _dst->d_v_ = D14{_alt.d_a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D14>(_dst->d_v_);
        if (_alt.d_a0) {
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
        }
      } else if (std::holds_alternative<D15>(_src->v())) {
        const auto &_alt = std::get<D15>(_src->v());
        _dst->d_v_ = D15{_alt.d_a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D15>(_dst->d_v_);
        if (_alt.d_a0) {
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
        }
      } else if (std::holds_alternative<D16>(_src->v())) {
        const auto &_alt = std::get<D16>(_src->v());
        _dst->d_v_ = D16{_alt.d_a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D16>(_dst->d_v_);
        if (_alt.d_a0) {
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
        }
      } else if (std::holds_alternative<D17>(_src->v())) {
        const auto &_alt = std::get<D17>(_src->v());
        _dst->d_v_ = D17{_alt.d_a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D17>(_dst->d_v_);
        if (_alt.d_a0) {
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
        }
      } else if (std::holds_alternative<D18>(_src->v())) {
        const auto &_alt = std::get<D18>(_src->v());
        _dst->d_v_ = D18{_alt.d_a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D18>(_dst->d_v_);
        if (_alt.d_a0) {
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
        }
      } else if (std::holds_alternative<D19>(_src->v())) {
        const auto &_alt = std::get<D19>(_src->v());
        _dst->d_v_ = D19{_alt.d_a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<D19>(_dst->d_v_);
        if (_alt.d_a0) {
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
        }
      } else if (std::holds_alternative<Da>(_src->v())) {
        const auto &_alt = std::get<Da>(_src->v());
        _dst->d_v_ = Da{_alt.d_a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<Da>(_dst->d_v_);
        if (_alt.d_a0) {
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
        }
      } else if (std::holds_alternative<Db>(_src->v())) {
        const auto &_alt = std::get<Db>(_src->v());
        _dst->d_v_ = Db{_alt.d_a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<Db>(_dst->d_v_);
        if (_alt.d_a0) {
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
        }
      } else if (std::holds_alternative<Dc>(_src->v())) {
        const auto &_alt = std::get<Dc>(_src->v());
        _dst->d_v_ = Dc{_alt.d_a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<Dc>(_dst->d_v_);
        if (_alt.d_a0) {
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
        }
      } else if (std::holds_alternative<Dd>(_src->v())) {
        const auto &_alt = std::get<Dd>(_src->v());
        _dst->d_v_ = Dd{_alt.d_a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<Dd>(_dst->d_v_);
        if (_alt.d_a0) {
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
        }
      } else if (std::holds_alternative<De>(_src->v())) {
        const auto &_alt = std::get<De>(_src->v());
        _dst->d_v_ = De{_alt.d_a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<De>(_dst->d_v_);
        if (_alt.d_a0) {
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
        }
      } else {
        const auto &_alt = std::get<Df>(_src->v());
        _dst->d_v_ = Df{_alt.d_a0 ? std::make_unique<Uint0>() : nullptr};
        auto &_dst_alt = std::get<Df>(_dst->d_v_);
        if (_alt.d_a0) {
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
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
    auto _drain = [&](Uint0 &_node) {
      if (std::holds_alternative<D10>(_node.d_v_)) {
        auto &_alt = std::get<D10>(_node.d_v_);
        if (_alt.d_a0) {
          _stack.push_back(std::move(_alt.d_a0));
        }
      }
      if (std::holds_alternative<D11>(_node.d_v_)) {
        auto &_alt = std::get<D11>(_node.d_v_);
        if (_alt.d_a0) {
          _stack.push_back(std::move(_alt.d_a0));
        }
      }
      if (std::holds_alternative<D12>(_node.d_v_)) {
        auto &_alt = std::get<D12>(_node.d_v_);
        if (_alt.d_a0) {
          _stack.push_back(std::move(_alt.d_a0));
        }
      }
      if (std::holds_alternative<D13>(_node.d_v_)) {
        auto &_alt = std::get<D13>(_node.d_v_);
        if (_alt.d_a0) {
          _stack.push_back(std::move(_alt.d_a0));
        }
      }
      if (std::holds_alternative<D14>(_node.d_v_)) {
        auto &_alt = std::get<D14>(_node.d_v_);
        if (_alt.d_a0) {
          _stack.push_back(std::move(_alt.d_a0));
        }
      }
      if (std::holds_alternative<D15>(_node.d_v_)) {
        auto &_alt = std::get<D15>(_node.d_v_);
        if (_alt.d_a0) {
          _stack.push_back(std::move(_alt.d_a0));
        }
      }
      if (std::holds_alternative<D16>(_node.d_v_)) {
        auto &_alt = std::get<D16>(_node.d_v_);
        if (_alt.d_a0) {
          _stack.push_back(std::move(_alt.d_a0));
        }
      }
      if (std::holds_alternative<D17>(_node.d_v_)) {
        auto &_alt = std::get<D17>(_node.d_v_);
        if (_alt.d_a0) {
          _stack.push_back(std::move(_alt.d_a0));
        }
      }
      if (std::holds_alternative<D18>(_node.d_v_)) {
        auto &_alt = std::get<D18>(_node.d_v_);
        if (_alt.d_a0) {
          _stack.push_back(std::move(_alt.d_a0));
        }
      }
      if (std::holds_alternative<D19>(_node.d_v_)) {
        auto &_alt = std::get<D19>(_node.d_v_);
        if (_alt.d_a0) {
          _stack.push_back(std::move(_alt.d_a0));
        }
      }
      if (std::holds_alternative<Da>(_node.d_v_)) {
        auto &_alt = std::get<Da>(_node.d_v_);
        if (_alt.d_a0) {
          _stack.push_back(std::move(_alt.d_a0));
        }
      }
      if (std::holds_alternative<Db>(_node.d_v_)) {
        auto &_alt = std::get<Db>(_node.d_v_);
        if (_alt.d_a0) {
          _stack.push_back(std::move(_alt.d_a0));
        }
      }
      if (std::holds_alternative<Dc>(_node.d_v_)) {
        auto &_alt = std::get<Dc>(_node.d_v_);
        if (_alt.d_a0) {
          _stack.push_back(std::move(_alt.d_a0));
        }
      }
      if (std::holds_alternative<Dd>(_node.d_v_)) {
        auto &_alt = std::get<Dd>(_node.d_v_);
        if (_alt.d_a0) {
          _stack.push_back(std::move(_alt.d_a0));
        }
      }
      if (std::holds_alternative<De>(_node.d_v_)) {
        auto &_alt = std::get<De>(_node.d_v_);
        if (_alt.d_a0) {
          _stack.push_back(std::move(_alt.d_a0));
        }
      }
      if (std::holds_alternative<Df>(_node.d_v_)) {
        auto &_alt = std::get<Df>(_node.d_v_);
        if (_alt.d_a0) {
          _stack.push_back(std::move(_alt.d_a0));
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
  static unsigned int tail_add(const unsigned int n, const unsigned int m);
  static unsigned int tail_addmul(const unsigned int r, const unsigned int n,
                                  const unsigned int m);
  static unsigned int tail_mul(const unsigned int n, const unsigned int m);
  static unsigned int of_uint_acc(const Uint &d, const unsigned int acc);
  static unsigned int of_uint(const Uint &d);
  static unsigned int of_hex_uint_acc(const Uint0 &d, const unsigned int acc);
  static unsigned int of_hex_uint(const Uint0 &d);
  static unsigned int of_num_uint(const Uint1 &d);
};

struct Spreadsheet {
  static inline const int64_t NUM_COLS = 104;
  static inline const int64_t NUM_ROWS = 100;
  static inline const int64_t GRID_SIZE =
      ((NUM_COLS * NUM_ROWS) & 0x7FFFFFFFFFFFFFFFLL);

  struct CellRef {
    int64_t ref_col;
    int64_t ref_row;

    // ACCESSORS
    CellRef clone() const {
      return CellRef{(*(this)).ref_col, (*(this)).ref_row};
    }
  };

  static bool cellref_eqb(const CellRef &r1, const CellRef &r2);
  static int64_t cell_index(const CellRef &r);

  struct Expr {
    // TYPES
    struct EInt {
      int64_t d_a0;
    };

    struct ERef {
      CellRef d_a0;
    };

    struct EAdd {
      std::unique_ptr<Expr> d_a0;
      std::unique_ptr<Expr> d_a1;
    };

    struct ESub {
      std::unique_ptr<Expr> d_a0;
      std::unique_ptr<Expr> d_a1;
    };

    struct EMul {
      std::unique_ptr<Expr> d_a0;
      std::unique_ptr<Expr> d_a1;
    };

    struct EDiv {
      std::unique_ptr<Expr> d_a0;
      std::unique_ptr<Expr> d_a1;
    };

    using variant_t = std::variant<EInt, ERef, EAdd, ESub, EMul, EDiv>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    Expr() {}

    explicit Expr(EInt _v) : d_v_(std::move(_v)) {}

    explicit Expr(ERef _v) : d_v_(std::move(_v)) {}

    explicit Expr(EAdd _v) : d_v_(std::move(_v)) {}

    explicit Expr(ESub _v) : d_v_(std::move(_v)) {}

    explicit Expr(EMul _v) : d_v_(std::move(_v)) {}

    explicit Expr(EDiv _v) : d_v_(std::move(_v)) {}

    Expr(const Expr &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    Expr(Expr &&_other) : d_v_(std::move(_other.d_v_)) {}

    Expr &operator=(const Expr &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    Expr &operator=(Expr &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    Expr clone() const {
      Expr _out{};

      struct _CloneFrame {
        const Expr *_src;
        Expr *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const Expr *_src = _frame._src;
        Expr *_dst = _frame._dst;
        if (std::holds_alternative<EInt>(_src->v())) {
          const auto &_alt = std::get<EInt>(_src->v());
          _dst->d_v_ = EInt{_alt.d_a0};
        } else if (std::holds_alternative<ERef>(_src->v())) {
          const auto &_alt = std::get<ERef>(_src->v());
          _dst->d_v_ = ERef{_alt.d_a0.clone()};
        } else if (std::holds_alternative<EAdd>(_src->v())) {
          const auto &_alt = std::get<EAdd>(_src->v());
          _dst->d_v_ = EAdd{_alt.d_a0 ? std::make_unique<Expr>() : nullptr,
                            _alt.d_a1 ? std::make_unique<Expr>() : nullptr};
          auto &_dst_alt = std::get<EAdd>(_dst->d_v_);
          if (_alt.d_a0) {
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          }
          if (_alt.d_a1) {
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          }
        } else if (std::holds_alternative<ESub>(_src->v())) {
          const auto &_alt = std::get<ESub>(_src->v());
          _dst->d_v_ = ESub{_alt.d_a0 ? std::make_unique<Expr>() : nullptr,
                            _alt.d_a1 ? std::make_unique<Expr>() : nullptr};
          auto &_dst_alt = std::get<ESub>(_dst->d_v_);
          if (_alt.d_a0) {
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          }
          if (_alt.d_a1) {
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          }
        } else if (std::holds_alternative<EMul>(_src->v())) {
          const auto &_alt = std::get<EMul>(_src->v());
          _dst->d_v_ = EMul{_alt.d_a0 ? std::make_unique<Expr>() : nullptr,
                            _alt.d_a1 ? std::make_unique<Expr>() : nullptr};
          auto &_dst_alt = std::get<EMul>(_dst->d_v_);
          if (_alt.d_a0) {
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          }
          if (_alt.d_a1) {
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          }
        } else {
          const auto &_alt = std::get<EDiv>(_src->v());
          _dst->d_v_ = EDiv{_alt.d_a0 ? std::make_unique<Expr>() : nullptr,
                            _alt.d_a1 ? std::make_unique<Expr>() : nullptr};
          auto &_dst_alt = std::get<EDiv>(_dst->d_v_);
          if (_alt.d_a0) {
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          }
          if (_alt.d_a1) {
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static Expr eint(int64_t a0) { return Expr(EInt{std::move(a0)}); }

    static Expr eref(CellRef a0) { return Expr(ERef{std::move(a0)}); }

    static Expr eadd(Expr a0, Expr a1) {
      return Expr(EAdd{std::make_unique<Expr>(std::move(a0)),
                       std::make_unique<Expr>(std::move(a1))});
    }

    static Expr esub(Expr a0, Expr a1) {
      return Expr(ESub{std::make_unique<Expr>(std::move(a0)),
                       std::make_unique<Expr>(std::move(a1))});
    }

    static Expr emul(Expr a0, Expr a1) {
      return Expr(EMul{std::make_unique<Expr>(std::move(a0)),
                       std::make_unique<Expr>(std::move(a1))});
    }

    static Expr ediv(Expr a0, Expr a1) {
      return Expr(EDiv{std::make_unique<Expr>(std::move(a0)),
                       std::make_unique<Expr>(std::move(a1))});
    }

    // MANIPULATORS
    ~Expr() {
      std::vector<std::unique_ptr<Expr>> _stack{};
      auto _drain = [&](Expr &_node) {
        if (std::holds_alternative<EAdd>(_node.d_v_)) {
          auto &_alt = std::get<EAdd>(_node.d_v_);
          if (_alt.d_a0) {
            _stack.push_back(std::move(_alt.d_a0));
          }
          if (_alt.d_a1) {
            _stack.push_back(std::move(_alt.d_a1));
          }
        }
        if (std::holds_alternative<ESub>(_node.d_v_)) {
          auto &_alt = std::get<ESub>(_node.d_v_);
          if (_alt.d_a0) {
            _stack.push_back(std::move(_alt.d_a0));
          }
          if (_alt.d_a1) {
            _stack.push_back(std::move(_alt.d_a1));
          }
        }
        if (std::holds_alternative<EMul>(_node.d_v_)) {
          auto &_alt = std::get<EMul>(_node.d_v_);
          if (_alt.d_a0) {
            _stack.push_back(std::move(_alt.d_a0));
          }
          if (_alt.d_a1) {
            _stack.push_back(std::move(_alt.d_a1));
          }
        }
        if (std::holds_alternative<EDiv>(_node.d_v_)) {
          auto &_alt = std::get<EDiv>(_node.d_v_);
          if (_alt.d_a0) {
            _stack.push_back(std::move(_alt.d_a0));
          }
          if (_alt.d_a1) {
            _stack.push_back(std::move(_alt.d_a1));
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

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }

    template <
        typename T1, MapsTo<T1, int64_t> F0, MapsTo<T1, CellRef> F1,
        MapsTo<T1, Expr, T1, Expr, T1> F2, MapsTo<T1, Expr, T1, Expr, T1> F3,
        MapsTo<T1, Expr, T1, Expr, T1> F4, MapsTo<T1, Expr, T1, Expr, T1> F5>
    T1 Expr_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename Expr::EInt>(_sv.v())) {
        const auto &[d_a0] = std::get<typename Expr::EInt>(_sv.v());
        return f(d_a0);
      } else if (std::holds_alternative<typename Expr::ERef>(_sv.v())) {
        const auto &[d_a0] = std::get<typename Expr::ERef>(_sv.v());
        return f0(d_a0);
      } else if (std::holds_alternative<typename Expr::EAdd>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename Expr::EAdd>(_sv.v());
        return f1(
            *(d_a0), (*(d_a0)).template Expr_rec<T1>(f, f0, f1, f2, f3, f4),
            *(d_a1), (*(d_a1)).template Expr_rec<T1>(f, f0, f1, f2, f3, f4));
      } else if (std::holds_alternative<typename Expr::ESub>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename Expr::ESub>(_sv.v());
        return f2(
            *(d_a0), (*(d_a0)).template Expr_rec<T1>(f, f0, f1, f2, f3, f4),
            *(d_a1), (*(d_a1)).template Expr_rec<T1>(f, f0, f1, f2, f3, f4));
      } else if (std::holds_alternative<typename Expr::EMul>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename Expr::EMul>(_sv.v());
        return f3(
            *(d_a0), (*(d_a0)).template Expr_rec<T1>(f, f0, f1, f2, f3, f4),
            *(d_a1), (*(d_a1)).template Expr_rec<T1>(f, f0, f1, f2, f3, f4));
      } else {
        const auto &[d_a0, d_a1] = std::get<typename Expr::EDiv>(_sv.v());
        return f4(
            *(d_a0), (*(d_a0)).template Expr_rec<T1>(f, f0, f1, f2, f3, f4),
            *(d_a1), (*(d_a1)).template Expr_rec<T1>(f, f0, f1, f2, f3, f4));
      }
    }

    template <
        typename T1, MapsTo<T1, int64_t> F0, MapsTo<T1, CellRef> F1,
        MapsTo<T1, Expr, T1, Expr, T1> F2, MapsTo<T1, Expr, T1, Expr, T1> F3,
        MapsTo<T1, Expr, T1, Expr, T1> F4, MapsTo<T1, Expr, T1, Expr, T1> F5>
    T1 Expr_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename Expr::EInt>(_sv.v())) {
        const auto &[d_a0] = std::get<typename Expr::EInt>(_sv.v());
        return f(d_a0);
      } else if (std::holds_alternative<typename Expr::ERef>(_sv.v())) {
        const auto &[d_a0] = std::get<typename Expr::ERef>(_sv.v());
        return f0(d_a0);
      } else if (std::holds_alternative<typename Expr::EAdd>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename Expr::EAdd>(_sv.v());
        return f1(
            *(d_a0), (*(d_a0)).template Expr_rect<T1>(f, f0, f1, f2, f3, f4),
            *(d_a1), (*(d_a1)).template Expr_rect<T1>(f, f0, f1, f2, f3, f4));
      } else if (std::holds_alternative<typename Expr::ESub>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename Expr::ESub>(_sv.v());
        return f2(
            *(d_a0), (*(d_a0)).template Expr_rect<T1>(f, f0, f1, f2, f3, f4),
            *(d_a1), (*(d_a1)).template Expr_rect<T1>(f, f0, f1, f2, f3, f4));
      } else if (std::holds_alternative<typename Expr::EMul>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename Expr::EMul>(_sv.v());
        return f3(
            *(d_a0), (*(d_a0)).template Expr_rect<T1>(f, f0, f1, f2, f3, f4),
            *(d_a1), (*(d_a1)).template Expr_rect<T1>(f, f0, f1, f2, f3, f4));
      } else {
        const auto &[d_a0, d_a1] = std::get<typename Expr::EDiv>(_sv.v());
        return f4(
            *(d_a0), (*(d_a0)).template Expr_rect<T1>(f, f0, f1, f2, f3, f4),
            *(d_a1), (*(d_a1)).template Expr_rect<T1>(f, f0, f1, f2, f3, f4));
      }
    }
  };

  struct Cell {
    // TYPES
    struct CEmpty {};

    struct CLit {
      int64_t d_a0;
    };

    struct CForm {
      Expr d_a0;
    };

    using variant_t = std::variant<CEmpty, CLit, CForm>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    Cell() {}

    explicit Cell(CEmpty _v) : d_v_(_v) {}

    explicit Cell(CLit _v) : d_v_(std::move(_v)) {}

    explicit Cell(CForm _v) : d_v_(std::move(_v)) {}

    Cell(const Cell &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    Cell(Cell &&_other) : d_v_(std::move(_other.d_v_)) {}

    Cell &operator=(const Cell &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    Cell &operator=(Cell &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    Cell clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<CEmpty>(_sv.v())) {
        return Cell(CEmpty{});
      } else if (std::holds_alternative<CLit>(_sv.v())) {
        const auto &[d_a0] = std::get<CLit>(_sv.v());
        return Cell(CLit{d_a0});
      } else {
        const auto &[d_a0] = std::get<CForm>(_sv.v());
        return Cell(CForm{d_a0.clone()});
      }
    }

    // CREATORS
    static Cell cempty() { return Cell(CEmpty{}); }

    static Cell clit(int64_t a0) { return Cell(CLit{std::move(a0)}); }

    static Cell cform(Expr a0) { return Cell(CForm{std::move(a0)}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, int64_t> F1, MapsTo<T1, Expr> F2>
  static T1 Cell_rect(const T1 f, F1 &&f0, F2 &&f1, const Cell &c) {
    if (std::holds_alternative<typename Cell::CEmpty>(c.v())) {
      return f;
    } else if (std::holds_alternative<typename Cell::CLit>(c.v())) {
      const auto &[d_a0] = std::get<typename Cell::CLit>(c.v());
      return f0(d_a0);
    } else {
      const auto &[d_a0] = std::get<typename Cell::CForm>(c.v());
      return f1(d_a0);
    }
  }

  template <typename T1, MapsTo<T1, int64_t> F1, MapsTo<T1, Expr> F2>
  static T1 Cell_rec(const T1 f, F1 &&f0, F2 &&f1, const Cell &c) {
    if (std::holds_alternative<typename Cell::CEmpty>(c.v())) {
      return f;
    } else if (std::holds_alternative<typename Cell::CLit>(c.v())) {
      const auto &[d_a0] = std::get<typename Cell::CLit>(c.v());
      return f0(d_a0);
    } else {
      const auto &[d_a0] = std::get<typename Cell::CForm>(c.v());
      return f1(d_a0);
    }
  }

  using Sheet = persistent_array<Cell>;
  static inline const Sheet new_sheet =
      persistent_array<Cell>(GRID_SIZE, Cell::cempty());
  static Cell get_cell(const persistent_array<Cell> s, const CellRef &r);
  static Sheet set_cell(const persistent_array<Cell> s, const CellRef &r,
                        const Cell &c);
  static bool mem_cellref(const CellRef &r, const List<CellRef> &xs);
  static std::optional<int64_t> eval_expr(const unsigned int fuel,
                                          List<CellRef> visited,
                                          const persistent_array<Cell> s,
                                          const Expr &e);
  static std::optional<int64_t>
  eval_cell(const unsigned int fuel, const persistent_array<Cell> s, CellRef r);
  static inline const unsigned int DEFAULT_FUEL = 100000u;
  static inline const std::optional<int64_t> smoke = []() {
    CellRef a1 = CellRef{0, 0};
    CellRef b1 = CellRef{1, 0};
    CellRef c1 = CellRef{2, 0};
    persistent_array<Cell> s1 = set_cell(new_sheet, a1, Cell::clit(INT64_C(2)));
    persistent_array<Cell> s2 = set_cell(s1, b1, Cell::clit(INT64_C(3)));
    persistent_array<Cell> s3 =
        set_cell(s2, c1,
                 Cell::cform(Expr::emul(Expr::eadd(Expr::eref(std::move(a1)),
                                                   Expr::eref(std::move(b1))),
                                        Expr::eint(INT64_C(7)))));
    return eval_cell(DEFAULT_FUEL, s3, std::move(c1));
  }();
};

#endif // INCLUDED_SPREADSHEET
