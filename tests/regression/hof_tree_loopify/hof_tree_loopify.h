#ifndef INCLUDED_HOF_TREE_LOOPIFY
#define INCLUDED_HOF_TREE_LOOPIFY

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct Uint {
  // TYPES
  struct Nil {};

  struct D0 {
    std::shared_ptr<Uint> d_a0;
  };

  struct D1 {
    std::shared_ptr<Uint> d_a0;
  };

  struct D2 {
    std::shared_ptr<Uint> d_a0;
  };

  struct D3 {
    std::shared_ptr<Uint> d_a0;
  };

  struct D4 {
    std::shared_ptr<Uint> d_a0;
  };

  struct D5 {
    std::shared_ptr<Uint> d_a0;
  };

  struct D6 {
    std::shared_ptr<Uint> d_a0;
  };

  struct D7 {
    std::shared_ptr<Uint> d_a0;
  };

  struct D8 {
    std::shared_ptr<Uint> d_a0;
  };

  struct D9 {
    std::shared_ptr<Uint> d_a0;
  };

  using variant_t = std::variant<Nil, D0, D1, D2, D3, D4, D5, D6, D7, D8, D9>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
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

  static std::shared_ptr<Uint> nil() { return std::make_shared<Uint>(Nil{}); }

  static std::shared_ptr<Uint> d0(const std::shared_ptr<Uint> &a0) {
    return std::make_shared<Uint>(D0{a0});
  }

  static std::shared_ptr<Uint> d0(std::shared_ptr<Uint> &&a0) {
    return std::make_shared<Uint>(D0{std::move(a0)});
  }

  static std::shared_ptr<Uint> d1(const std::shared_ptr<Uint> &a0) {
    return std::make_shared<Uint>(D1{a0});
  }

  static std::shared_ptr<Uint> d1(std::shared_ptr<Uint> &&a0) {
    return std::make_shared<Uint>(D1{std::move(a0)});
  }

  static std::shared_ptr<Uint> d2(const std::shared_ptr<Uint> &a0) {
    return std::make_shared<Uint>(D2{a0});
  }

  static std::shared_ptr<Uint> d2(std::shared_ptr<Uint> &&a0) {
    return std::make_shared<Uint>(D2{std::move(a0)});
  }

  static std::shared_ptr<Uint> d3(const std::shared_ptr<Uint> &a0) {
    return std::make_shared<Uint>(D3{a0});
  }

  static std::shared_ptr<Uint> d3(std::shared_ptr<Uint> &&a0) {
    return std::make_shared<Uint>(D3{std::move(a0)});
  }

  static std::shared_ptr<Uint> d4(const std::shared_ptr<Uint> &a0) {
    return std::make_shared<Uint>(D4{a0});
  }

  static std::shared_ptr<Uint> d4(std::shared_ptr<Uint> &&a0) {
    return std::make_shared<Uint>(D4{std::move(a0)});
  }

  static std::shared_ptr<Uint> d5(const std::shared_ptr<Uint> &a0) {
    return std::make_shared<Uint>(D5{a0});
  }

  static std::shared_ptr<Uint> d5(std::shared_ptr<Uint> &&a0) {
    return std::make_shared<Uint>(D5{std::move(a0)});
  }

  static std::shared_ptr<Uint> d6(const std::shared_ptr<Uint> &a0) {
    return std::make_shared<Uint>(D6{a0});
  }

  static std::shared_ptr<Uint> d6(std::shared_ptr<Uint> &&a0) {
    return std::make_shared<Uint>(D6{std::move(a0)});
  }

  static std::shared_ptr<Uint> d7(const std::shared_ptr<Uint> &a0) {
    return std::make_shared<Uint>(D7{a0});
  }

  static std::shared_ptr<Uint> d7(std::shared_ptr<Uint> &&a0) {
    return std::make_shared<Uint>(D7{std::move(a0)});
  }

  static std::shared_ptr<Uint> d8(const std::shared_ptr<Uint> &a0) {
    return std::make_shared<Uint>(D8{a0});
  }

  static std::shared_ptr<Uint> d8(std::shared_ptr<Uint> &&a0) {
    return std::make_shared<Uint>(D8{std::move(a0)});
  }

  static std::shared_ptr<Uint> d9(const std::shared_ptr<Uint> &a0) {
    return std::make_shared<Uint>(D9{a0});
  }

  static std::shared_ptr<Uint> d9(std::shared_ptr<Uint> &&a0) {
    return std::make_shared<Uint>(D9{std::move(a0)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct Uint0 {
  // TYPES
  struct Nil0 {};

  struct D10 {
    std::shared_ptr<Uint0> d_a0;
  };

  struct D11 {
    std::shared_ptr<Uint0> d_a0;
  };

  struct D12 {
    std::shared_ptr<Uint0> d_a0;
  };

  struct D13 {
    std::shared_ptr<Uint0> d_a0;
  };

  struct D14 {
    std::shared_ptr<Uint0> d_a0;
  };

  struct D15 {
    std::shared_ptr<Uint0> d_a0;
  };

  struct D16 {
    std::shared_ptr<Uint0> d_a0;
  };

  struct D17 {
    std::shared_ptr<Uint0> d_a0;
  };

  struct D18 {
    std::shared_ptr<Uint0> d_a0;
  };

  struct D19 {
    std::shared_ptr<Uint0> d_a0;
  };

  struct Da {
    std::shared_ptr<Uint0> d_a0;
  };

  struct Db {
    std::shared_ptr<Uint0> d_a0;
  };

  struct Dc {
    std::shared_ptr<Uint0> d_a0;
  };

  struct Dd {
    std::shared_ptr<Uint0> d_a0;
  };

  struct De {
    std::shared_ptr<Uint0> d_a0;
  };

  struct Df {
    std::shared_ptr<Uint0> d_a0;
  };

  using variant_t = std::variant<Nil0, D10, D11, D12, D13, D14, D15, D16, D17,
                                 D18, D19, Da, Db, Dc, Dd, De, Df>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
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

  static std::shared_ptr<Uint0> nil0() {
    return std::make_shared<Uint0>(Nil0{});
  }

  static std::shared_ptr<Uint0> d10(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(D10{a0});
  }

  static std::shared_ptr<Uint0> d10(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(D10{std::move(a0)});
  }

  static std::shared_ptr<Uint0> d11(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(D11{a0});
  }

  static std::shared_ptr<Uint0> d11(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(D11{std::move(a0)});
  }

  static std::shared_ptr<Uint0> d12(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(D12{a0});
  }

  static std::shared_ptr<Uint0> d12(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(D12{std::move(a0)});
  }

  static std::shared_ptr<Uint0> d13(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(D13{a0});
  }

  static std::shared_ptr<Uint0> d13(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(D13{std::move(a0)});
  }

  static std::shared_ptr<Uint0> d14(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(D14{a0});
  }

  static std::shared_ptr<Uint0> d14(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(D14{std::move(a0)});
  }

  static std::shared_ptr<Uint0> d15(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(D15{a0});
  }

  static std::shared_ptr<Uint0> d15(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(D15{std::move(a0)});
  }

  static std::shared_ptr<Uint0> d16(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(D16{a0});
  }

  static std::shared_ptr<Uint0> d16(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(D16{std::move(a0)});
  }

  static std::shared_ptr<Uint0> d17(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(D17{a0});
  }

  static std::shared_ptr<Uint0> d17(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(D17{std::move(a0)});
  }

  static std::shared_ptr<Uint0> d18(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(D18{a0});
  }

  static std::shared_ptr<Uint0> d18(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(D18{std::move(a0)});
  }

  static std::shared_ptr<Uint0> d19(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(D19{a0});
  }

  static std::shared_ptr<Uint0> d19(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(D19{std::move(a0)});
  }

  static std::shared_ptr<Uint0> da(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(Da{a0});
  }

  static std::shared_ptr<Uint0> da(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(Da{std::move(a0)});
  }

  static std::shared_ptr<Uint0> db(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(Db{a0});
  }

  static std::shared_ptr<Uint0> db(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(Db{std::move(a0)});
  }

  static std::shared_ptr<Uint0> dc(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(Dc{a0});
  }

  static std::shared_ptr<Uint0> dc(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(Dc{std::move(a0)});
  }

  static std::shared_ptr<Uint0> dd(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(Dd{a0});
  }

  static std::shared_ptr<Uint0> dd(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(Dd{std::move(a0)});
  }

  static std::shared_ptr<Uint0> de(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(De{a0});
  }

  static std::shared_ptr<Uint0> de(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(De{std::move(a0)});
  }

  static std::shared_ptr<Uint0> df(const std::shared_ptr<Uint0> &a0) {
    return std::make_shared<Uint0>(Df{a0});
  }

  static std::shared_ptr<Uint0> df(std::shared_ptr<Uint0> &&a0) {
    return std::make_shared<Uint0>(Df{std::move(a0)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct Uint1 {
  // TYPES
  struct UIntDecimal {
    std::shared_ptr<Uint> d_u;
  };

  struct UIntHexadecimal {
    std::shared_ptr<Uint0> d_u;
  };

  using variant_t = std::variant<UIntDecimal, UIntHexadecimal>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit Uint1(UIntDecimal _v) : d_v_(std::move(_v)) {}

  explicit Uint1(UIntHexadecimal _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<Uint1> uintdecimal(const std::shared_ptr<Uint> &u) {
    return std::make_shared<Uint1>(UIntDecimal{u});
  }

  static std::shared_ptr<Uint1> uintdecimal(std::shared_ptr<Uint> &&u) {
    return std::make_shared<Uint1>(UIntDecimal{std::move(u)});
  }

  static std::shared_ptr<Uint1>
  uinthexadecimal(const std::shared_ptr<Uint0> &u) {
    return std::make_shared<Uint1>(UIntHexadecimal{u});
  }

  static std::shared_ptr<Uint1> uinthexadecimal(std::shared_ptr<Uint0> &&u) {
    return std::make_shared<Uint1>(UIntHexadecimal{std::move(u)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct Nat {
  __attribute__((pure)) static unsigned int tail_add(const unsigned int n,
                                                     const unsigned int m);
  __attribute__((pure)) static unsigned int
  tail_addmul(const unsigned int r, const unsigned int n, const unsigned int m);
  __attribute__((pure)) static unsigned int tail_mul(const unsigned int n,
                                                     const unsigned int m);
  __attribute__((pure)) static unsigned int
  of_uint_acc(const std::shared_ptr<Uint> &d, const unsigned int acc);
  __attribute__((pure)) static unsigned int
  of_uint(const std::shared_ptr<Uint> &d);
  __attribute__((pure)) static unsigned int
  of_hex_uint_acc(const std::shared_ptr<Uint0> &d, const unsigned int acc);
  __attribute__((pure)) static unsigned int
  of_hex_uint(const std::shared_ptr<Uint0> &d);
  __attribute__((pure)) static unsigned int
  of_num_uint(const std::shared_ptr<Uint1> &d);
};

struct HofTreeLoopify {
  template <typename t_A> struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<tree<t_A>> d_a0;
      t_A d_a1;
      std::shared_ptr<tree<t_A>> d_a2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit tree(Leaf _v) : d_v_(_v) {}

    explicit tree(Node _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<tree<t_A>> leaf() {
      return std::make_shared<tree<t_A>>(Leaf{});
    }

    static std::shared_ptr<tree<t_A>>
    node(const std::shared_ptr<tree<t_A>> &a0, t_A a1,
         const std::shared_ptr<tree<t_A>> &a2) {
      return std::make_shared<tree<t_A>>(Node{a0, std::move(a1), a2});
    }

    static std::shared_ptr<tree<t_A>> node(std::shared_ptr<tree<t_A>> &&a0,
                                           t_A a1,
                                           std::shared_ptr<tree<t_A>> &&a2) {
      return std::make_shared<tree<t_A>>(
          Node{std::move(a0), std::move(a1), std::move(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2,
            MapsTo<T2, std::shared_ptr<tree<T1>>, T2, T1,
                   std::shared_ptr<tree<T1>>, T2>
                F1>
  static T2 tree_rect(const T2 f, F1 &&f0, const std::shared_ptr<tree<T1>> &t) {
    struct _Enter {
      const std::shared_ptr<tree<T1>> t;
    };

    struct _Call1 {
      std::shared_ptr<tree<T1>> _s0;
      std::shared_ptr<tree<T1>> _s1;
      T1 _s2;
      std::shared_ptr<tree<T1>> _s3;
    };

    struct _Call2 {
      T2 _s0;
      std::shared_ptr<tree<T1>> _s1;
      T1 _s2;
      std::shared_ptr<tree<T1>> _s3;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.emplace_back(_Enter{t});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        const auto &_f = std::get<_Enter>(_frame);
        const std::shared_ptr<tree<T1>> t = _f.t;
        if (std::holds_alternative<typename tree<T1>::Leaf>(t->v())) {
          _result = f;
        } else {
          const auto &[d_a0, d_a1, d_a2] =
              std::get<typename tree<T1>::Node>(t->v());
          _stack.emplace_back(_Call1{d_a0, d_a2, d_a1, d_a0});
          _stack.emplace_back(_Enter{d_a2});
        }
      } else if (std::holds_alternative<_Call1>(_frame)) {
        const auto &_f = std::get<_Call1>(_frame);
        _stack.emplace_back(_Call2{_result, _f._s1, _f._s2, _f._s3});
        _stack.emplace_back(_Enter{_f._s0});
      } else {
        const auto &_f = std::get<_Call2>(_frame);
        _result = f0(_f._s3, _result, _f._s2, _f._s1, _f._s0);
      }
    }
    return _result;
  }

  template <typename T1, typename T2,
            MapsTo<T2, std::shared_ptr<tree<T1>>, T2, T1,
                   std::shared_ptr<tree<T1>>, T2>
                F1>
  static T2 tree_rec(const T2 f, F1 &&f0, const std::shared_ptr<tree<T1>> &t) {
    struct _Enter {
      const std::shared_ptr<tree<T1>> t;
    };

    struct _Call1 {
      std::shared_ptr<tree<T1>> _s0;
      std::shared_ptr<tree<T1>> _s1;
      T1 _s2;
      std::shared_ptr<tree<T1>> _s3;
    };

    struct _Call2 {
      T2 _s0;
      std::shared_ptr<tree<T1>> _s1;
      T1 _s2;
      std::shared_ptr<tree<T1>> _s3;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.emplace_back(_Enter{t});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        const auto &_f = std::get<_Enter>(_frame);
        const std::shared_ptr<tree<T1>> t = _f.t;
        if (std::holds_alternative<typename tree<T1>::Leaf>(t->v())) {
          _result = f;
        } else {
          const auto &[d_a0, d_a1, d_a2] =
              std::get<typename tree<T1>::Node>(t->v());
          _stack.emplace_back(_Call1{d_a0, d_a2, d_a1, d_a0});
          _stack.emplace_back(_Enter{d_a2});
        }
      } else if (std::holds_alternative<_Call1>(_frame)) {
        const auto &_f = std::get<_Call1>(_frame);
        _stack.emplace_back(_Call2{_result, _f._s1, _f._s2, _f._s3});
        _stack.emplace_back(_Enter{_f._s0});
      } else {
        const auto &_f = std::get<_Call2>(_frame);
        _result = f0(_f._s3, _result, _f._s2, _f._s1, _f._s0);
      }
    }
    return _result;
  }

  static std::shared_ptr<tree<unsigned int>> depth_tree(const unsigned int n);

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static std::shared_ptr<tree<T2>>
  tree_map(F0 &&f, const std::shared_ptr<tree<T1>> &t) {
    struct _Enter {
      const std::shared_ptr<tree<T1>> t;
    };

    struct _Call1 {
      std::shared_ptr<tree<T1>> _s0;
      T2 _s1;
    };

    struct _Call2 {
      std::shared_ptr<tree<T2>> _s0;
      T2 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    std::shared_ptr<tree<T2>> _result{};
    std::vector<_Frame> _stack;
    _stack.emplace_back(_Enter{t});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        const auto &_f = std::get<_Enter>(_frame);
        const std::shared_ptr<tree<T1>> t = _f.t;
        if (std::holds_alternative<typename tree<T1>::Leaf>(t->v())) {
          _result = tree<T2>::leaf();
        } else {
          const auto &[d_a0, d_a1, d_a2] =
              std::get<typename tree<T1>::Node>(t->v());
          _stack.emplace_back(_Call1{d_a0, f(d_a1)});
          _stack.emplace_back(_Enter{d_a2});
        }
      } else if (std::holds_alternative<_Call1>(_frame)) {
        const auto &_f = std::get<_Call1>(_frame);
        _stack.emplace_back(_Call2{_result, _f._s1});
        _stack.emplace_back(_Enter{_f._s0});
      } else {
        const auto &_f = std::get<_Call2>(_frame);
        _result = tree<T2>::node(_result, _f._s1, _f._s0);
      }
    }
    return _result;
  }

  template <typename T1, typename T2, MapsTo<T2, T2, T1, T2> F1>
  static T2 tree_fold(const T2 base, F1 &&f,
                      const std::shared_ptr<tree<T1>> &t) {
    struct _Enter {
      const std::shared_ptr<tree<T1>> t;
    };

    struct _Call1 {
      std::shared_ptr<tree<T1>> _s0;
      T1 _s1;
    };

    struct _Call2 {
      T2 _s0;
      T1 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.emplace_back(_Enter{t});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        const auto &_f = std::get<_Enter>(_frame);
        const std::shared_ptr<tree<T1>> t = _f.t;
        if (std::holds_alternative<typename tree<T1>::Leaf>(t->v())) {
          _result = base;
        } else {
          const auto &[d_a0, d_a1, d_a2] =
              std::get<typename tree<T1>::Node>(t->v());
          _stack.emplace_back(_Call1{d_a0, d_a1});
          _stack.emplace_back(_Enter{d_a2});
        }
      } else if (std::holds_alternative<_Call1>(_frame)) {
        const auto &_f = std::get<_Call1>(_frame);
        _stack.emplace_back(_Call2{_result, _f._s1});
        _stack.emplace_back(_Enter{_f._s0});
      } else {
        const auto &_f = std::get<_Call2>(_frame);
        _result = f(_result, _f._s1, _f._s0);
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1, T2> F0>
  static std::shared_ptr<tree<T3>>
  tree_zip_with(F0 &&f, const std::shared_ptr<tree<T1>> &t1,
                const std::shared_ptr<tree<T2>> &t2) {
    struct _Enter {
      const std::shared_ptr<tree<T2>> t2;
      const std::shared_ptr<tree<T1>> t1;
    };

    struct _Call1 {
      std::shared_ptr<tree<T2>> _s0;
      std::shared_ptr<tree<T1>> _s1;
      T3 _s2;
    };

    struct _Call2 {
      std::shared_ptr<tree<T3>> _s0;
      T3 _s1;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    std::shared_ptr<tree<T3>> _result{};
    std::vector<_Frame> _stack;
    _stack.emplace_back(_Enter{t2, t1});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        const auto &_f = std::get<_Enter>(_frame);
        const std::shared_ptr<tree<T2>> t2 = _f.t2;
        const std::shared_ptr<tree<T1>> t1 = _f.t1;
        if (std::holds_alternative<typename tree<T1>::Leaf>(t1->v())) {
          _result = tree<T3>::leaf();
        } else {
          const auto &[d_a0, d_a1, d_a2] =
              std::get<typename tree<T1>::Node>(t1->v());
          if (std::holds_alternative<typename tree<T2>::Leaf>(t2->v())) {
            _result = tree<T3>::leaf();
          } else {
            const auto &[d_a00, d_a10, d_a20] =
                std::get<typename tree<T2>::Node>(t2->v());
            _stack.emplace_back(_Call1{d_a00, d_a0, f(d_a1, d_a10)});
            _stack.emplace_back(_Enter{d_a20, d_a2});
          }
        }
      } else if (std::holds_alternative<_Call1>(_frame)) {
        const auto &_f = std::get<_Call1>(_frame);
        _stack.emplace_back(_Call2{_result, _f._s2});
        _stack.emplace_back(_Enter{_f._s0, _f._s1});
      } else {
        const auto &_f = std::get<_Call2>(_frame);
        _result = tree<T3>::node(_result, _f._s1, _f._s0);
      }
    }
    return _result;
  }

  template <typename T1, typename T2, typename T3,
            MapsTo<std::pair<T3, T2>, T3, T1> F0>
  __attribute__((pure)) static std::pair<T3, std::shared_ptr<tree<T2>>>
  tree_map_accum(F0 &&f, const T3 acc, const std::shared_ptr<tree<T1>> &t) {
    struct _Enter {
      const std::shared_ptr<tree<T1>> t;
      const T3 acc;
    };

    struct _Call1 {
      F0 _s0;
      T1 _s1;
      std::shared_ptr<tree<T1>> _s2;
    };

    struct _Call2 {
      T2 _s0;
      std::shared_ptr<tree<T2>> _s1;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    std::pair<T3, std::shared_ptr<tree<T2>>> _result{};
    std::vector<_Frame> _stack;
    _stack.emplace_back(_Enter{t, acc});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        const auto &_f = std::get<_Enter>(_frame);
        const std::shared_ptr<tree<T1>> t = _f.t;
        const T3 acc = _f.acc;
        if (std::holds_alternative<typename tree<T1>::Leaf>(t->v())) {
          _result = std::make_pair(acc, tree<T2>::leaf());
        } else {
          const auto &[d_a0, d_a1, d_a2] =
              std::get<typename tree<T1>::Node>(t->v());
          _stack.emplace_back(_Call1{f, d_a1, d_a2});
          _stack.emplace_back(_Enter{d_a0, acc});
        }
      } else if (std::holds_alternative<_Call1>(_frame)) {
        const auto &_f = std::get<_Call1>(_frame);
        F0 f = _f._s0;
        T1 d_a1 = _f._s1;
        std::shared_ptr<tree<T1>> d_a2 = _f._s2;
        const T3 &acc1 = _result.first;
        const std::shared_ptr<tree<T2>> &l_ = _result.second;
        auto _cs = f(acc1, d_a1);
        const T3 &acc2 = _cs.first;
        const T2 &x_ = _cs.second;
        _stack.emplace_back(_Call2{x_, l_});
        _stack.emplace_back(_Enter{d_a2, acc2});
      } else {
        const auto &_f = std::get<_Call2>(_frame);
        T2 x_ = _f._s0;
        std::shared_ptr<tree<T2>> l_ = _f._s1;
        const T3 &acc3 = _result.first;
        const std::shared_ptr<tree<T2>> &r_ = _result.second;
        _result = std::make_pair(acc3, tree<T2>::node(l_, x_, r_));
      }
    }
    return _result;
  }

  static inline const std::shared_ptr<tree<unsigned int>> small_tree =
      tree<unsigned int>::node(
          tree<unsigned int>::node(
              tree<unsigned int>::node(tree<unsigned int>::leaf(), 1u,
                                       tree<unsigned int>::leaf()),
              2u,
              tree<unsigned int>::node(tree<unsigned int>::leaf(), 3u,
                                       tree<unsigned int>::leaf())),
          4u,
          tree<unsigned int>::node(
              tree<unsigned int>::node(tree<unsigned int>::leaf(), 5u,
                                       tree<unsigned int>::leaf()),
              6u,
              tree<unsigned int>::node(tree<unsigned int>::leaf(), 7u,
                                       tree<unsigned int>::leaf())));
  static inline const std::shared_ptr<tree<unsigned int>> mapped =
      tree_map<unsigned int, unsigned int>(
          [](const unsigned int x) { return (x * 2u); }, small_tree);
  static inline const unsigned int folded =
      tree_fold<unsigned int, unsigned int>(
          0u,
          [](const unsigned int l, const unsigned int x, const unsigned int r) {
            return ((l + x) + r);
          },
          small_tree);
  static inline const std::shared_ptr<tree<unsigned int>> zipped =
      tree_zip_with<unsigned int, unsigned int, unsigned int>(
          [](unsigned int _x0, unsigned int _x1) -> unsigned int {
            return (_x0 + _x1);
          },
          small_tree, small_tree);
  static inline const std::pair<unsigned int,
                                std::shared_ptr<tree<unsigned int>>>
      accum = tree_map_accum<unsigned int, unsigned int, unsigned int>(
          [](const unsigned int s, const unsigned int x) {
            return std::make_pair((s + x), s);
          },
          0u, small_tree);
  static inline const std::shared_ptr<tree<unsigned int>> deep =
      depth_tree(50000u);
};

#endif // INCLUDED_HOF_TREE_LOOPIFY
