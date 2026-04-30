#ifndef INCLUDED_TOKENIZER
#define INCLUDED_TOKENIZER

#include <cstdint>
#include <functional>
#include <memory>
#include <optional>
#include <string>
#include <string_view>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

using namespace std::string_literals;
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

  List<t_A> rev() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return List<t_A>::nil();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return (*(d_a1)).rev().app(List<t_A>::cons(d_a0, List<t_A>::nil()));
    }
  }

  List<t_A> app(List<t_A> m) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return m;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return List<t_A>::cons(d_a0, (*(d_a1)).app(std::move(m)));
    }
  }
};

struct ToString {
  template <typename T1, typename T2, MapsTo<std::string, T1> F0,
            MapsTo<std::string, T2> F1>
  static std::string pair_to_string(F0 &&p1, F1 &&p2,
                                    const std::pair<T1, T2> &x) {
    const T1 &a = x.first;
    const T2 &b = x.second;
    return "("s + p1(a) + ", "s + p2(b) + ")"s;
  }

  template <typename T1, MapsTo<std::string, T1> F0>
  static std::string intersperse(F0 &&p, const std::string sep,
                                 const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return "";
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
      auto &&_sv = *(d_a1);
      if (std::holds_alternative<typename List<T1>::Nil>(_sv.v())) {
        return sep + p(d_a0);
      } else {
        return sep + p(d_a0) + intersperse<T1>(p, sep, *(d_a1));
      }
    }
  }

  template <typename T1, MapsTo<std::string, T1> F0>
  static std::string list_to_string(F0 &&p, const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return "[]";
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
      auto &&_sv = *(d_a1);
      if (std::holds_alternative<typename List<T1>::Nil>(_sv.v())) {
        return "["s + p(d_a0) + "]"s;
      } else {
        return "["s + p(d_a0) + intersperse<T1>(p, "; ", *(d_a1)) + "]"s;
      }
    }
  }
};

struct Tokenizer {
  static std::pair<std::optional<std::basic_string_view<char>>,
                   std::basic_string_view<char>>
  next_token(const std::basic_string_view<char> input,
             const std::basic_string_view<char> soft,
             const std::basic_string_view<char> hard);
  static List<std::basic_string_view<char>>
  list_tokens(const std::basic_string_view<char> input,
              const std::basic_string_view<char> soft,
              const std::basic_string_view<char> hard);

  template <typename T1>
  static std::vector<T1> list_to_vec_h(const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return {};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
      std::vector<T1> v = list_to_vec_h<T1>(*(d_a1));
      v.push_back(d_a0);
      return v;
    }
  }

  template <typename T1> static std::vector<T1> list_to_vec(const List<T1> &l) {
    return list_to_vec_h<T1>(l.rev());
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static std::vector<T2> list_to_vec_map_h(F0 &&f, const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return {};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
      std::vector<T2> v = list_to_vec_map_h<T1, T2>(f, *(d_a1));
      v.push_back(f(d_a0));
      return v;
    }
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static std::vector<T2> list_to_vec_map(F0 &&f, const List<T1> &l) {
    return list_to_vec_map_h<T1, T2>(f, l.rev());
  }
};

#endif // INCLUDED_TOKENIZER
