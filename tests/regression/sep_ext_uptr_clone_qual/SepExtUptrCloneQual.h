#ifndef INCLUDED_SEPEXTUPTRCLONEQUAL
#define INCLUDED_SEPEXTUPTRCLONEQUAL

#include <memory>
#include <utility>
#include <variant>
#include <vector>

namespace SepExtUptrCloneQual {

template <typename M>
concept OrderedType = requires { typename M::t; };

template <typename A> struct MyList {
  // TYPES
  struct Mynil {};

  struct Mycons {
    A a0;
    std::unique_ptr<MyList<A>> a1;
  };

  using variant_t = std::variant<Mynil, Mycons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  MyList() {}

  explicit MyList(Mynil _v) : v_(_v) {}

  explicit MyList(Mycons _v) : v_(std::move(_v)) {}

  MyList(const MyList<A> &_other) : v_(std::move(_other.clone().v_)) {}

  MyList(MyList<A> &&_other) : v_(std::move(_other.v_)) {}

  MyList<A> &operator=(const MyList<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  MyList<A> &operator=(MyList<A> &&_other) {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  MyList<A> clone() const {
    MyList<A> _out{};

    struct _CloneFrame {
      const MyList<A> *_src;
      MyList<A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const MyList<A> *_src = _frame._src;
      MyList<A> *_dst = _frame._dst;
      if (std::holds_alternative<Mynil>(_src->v())) {
        _dst->v_ = Mynil{};
      } else {
        const auto &_alt = std::get<Mycons>(_src->v());
        _dst->v_ =
            Mycons{_alt.a0, _alt.a1 ? std::make_unique<MyList<A>>() : nullptr};
        auto &_dst_alt = std::get<Mycons>(_dst->v_);
        if (_alt.a1) {
          _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit MyList(const MyList<_U> &_other) {
    if (std::holds_alternative<typename MyList<_U>::Mynil>(_other.v())) {
      this->v_ = Mynil{};
    } else {
      const auto &[a0, a1] = std::get<typename MyList<_U>::Mycons>(_other.v());
      this->v_ = Mycons{A(a0), a1 ? std::make_unique<MyList<A>>(*a1) : nullptr};
    }
  }

  static MyList<A> mynil() { return MyList(Mynil{}); }

  static MyList<A> mycons(A a0, MyList<A> a1) {
    return MyList(
        Mycons{std::move(a0), std::make_unique<MyList<A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~MyList() {
    std::vector<std::unique_ptr<MyList<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](MyList<A> &_node) {
      if (std::holds_alternative<Mycons>(_node.v_)) {
        auto &_alt = std::get<Mycons>(_node.v_);
        if (_alt.a1) {
          _stack.push_back(std::move(_alt.a1));
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

template <OrderedType X> struct FMap {
  template <typename T1>
  static MyList<std::pair<typename X::t, T1>>
  tail(const MyList<std::pair<typename X::t, T1>> &l) {
    if (std::holds_alternative<
            typename MyList<std::pair<typename X::t, T1>>::Mynil>(l.v())) {
      return MyList<std::pair<typename X::t, T1>>::mynil();
    } else {
      const auto &[a0, a1] =
          std::get<typename MyList<std::pair<typename X::t, T1>>::Mycons>(
              l.v());
      return *a1;
    }
  }
};

} // namespace SepExtUptrCloneQual

#endif // INCLUDED_SEPEXTUPTRCLONEQUAL
