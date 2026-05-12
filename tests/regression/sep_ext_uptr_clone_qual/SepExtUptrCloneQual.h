#ifndef INCLUDED_SEPEXTUPTRCLONEQUAL
#define INCLUDED_SEPEXTUPTRCLONEQUAL

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

namespace SepExtUptrCloneQual {

template <typename M>
concept OrderedType = requires { typename M::t; };

template <typename t_A> struct MyList {
  // TYPES
  struct Mynil {};

  struct Mycons {
    t_A d_a0;
    std::unique_ptr<MyList<t_A>> d_a1;
  };

  using variant_t = std::variant<Mynil, Mycons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  MyList() {}

  explicit MyList(Mynil _v) : d_v_(_v) {}

  explicit MyList(Mycons _v) : d_v_(std::move(_v)) {}

  MyList(const MyList<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  MyList(MyList<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  MyList<t_A> &operator=(const MyList<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  MyList<t_A> &operator=(MyList<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  MyList<t_A> clone() const {
    MyList<t_A> _out{};

    struct _CloneFrame {
      const MyList<t_A> *_src;
      MyList<t_A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const MyList<t_A> *_src = _frame._src;
      MyList<t_A> *_dst = _frame._dst;
      if (std::holds_alternative<Mynil>(_src->v())) {
        _dst->d_v_ = Mynil();
      } else {
        const auto &_alt = std::get<Mycons>(_src->v());
        _dst->d_v_ = Mycons(
            _alt.d_a0, _alt.d_a1 ? std::make_unique<MyList<t_A>>() : nullptr);
        auto &_dst_alt = std::get<Mycons>(_dst->d_v_);
        if (_alt.d_a1) {
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit MyList(const MyList<_U> &_other) {
    if (std::holds_alternative<typename MyList<_U>::Mynil>(_other.v())) {
      this->d_v_ = Mynil();
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename MyList<_U>::Mycons>(_other.v());
      this->d_v_ = Mycons(t_A(d_a0), d_a1 ? std::make_unique<MyList<t_A>>(*d_a1)
                                          : nullptr);
    }
  }

  static MyList<t_A> mynil() { return MyList(Mynil()); }

  static MyList<t_A> mycons(t_A a0, MyList<t_A> a1) {
    return MyList(
        Mycons(std::move(a0), std::make_unique<MyList<t_A>>(std::move(a1))));
  }

  // MANIPULATORS
  ~MyList() {
    std::vector<std::unique_ptr<MyList<t_A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](MyList<t_A> &_node) {
      if (std::holds_alternative<Mycons>(_node.d_v_)) {
        auto &_alt = std::get<Mycons>(_node.d_v_);
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

template <OrderedType X> struct FMap {
  template <typename T1>
  static MyList<std::pair<typename X::t, T1>>
  tail(const MyList<std::pair<typename X::t, T1>> &l) {
    if (std::holds_alternative<
            typename MyList<std::pair<typename X::t, T1>>::Mynil>(l.v())) {
      return MyList<std::pair<typename X::t, T1>>::mynil();
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename MyList<std::pair<typename X::t, T1>>::Mycons>(
              l.v());
      return *(d_a1);
    }
  }
};

} // namespace SepExtUptrCloneQual

#endif // INCLUDED_SEPEXTUPTRCLONEQUAL
