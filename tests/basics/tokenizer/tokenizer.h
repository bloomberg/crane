#ifndef INCLUDED_TOKENIZER
#define INCLUDED_TOKENIZER

#include <cstdint>
#include <memory>
#include <optional>
#include <string>
#include <string_view>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

using namespace std::string_literals;

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a0;
    std::unique_ptr<List<A>> a1;
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
        _dst->v_ =
            Cons{_alt.a0, _alt.a1 ? std::make_unique<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.a1) {
          _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
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
      const auto &[a0, a1] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a0), a1 ? std::make_unique<List<A>>(*a1) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a0, List<A> a1) {
    return List(Cons{std::move(a0), std::make_unique<List<A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
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

  List<A> rev() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return List<A>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return a1->rev().app(List<A>::cons(a0, List<A>::nil()));
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

struct ToString {
  template <typename T1, typename T2, typename F0, typename F1>
    requires std::is_invocable_r_v<std::string, F0 &, T1 &> &&
             std::is_invocable_r_v<std::string, F1 &, T2 &>
  static std::string pair_to_string(F0 &&p1, F1 &&p2,
                                    const std::pair<T1, T2> &x) {
    const T1 &a = x.first;
    const T2 &b = x.second;
    return "("s + p1(a) + ", "s + p2(b) + ")"s;
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<std::string, F0 &, T1 &>
  static std::string intersperse(F0 &&p, std::string sep, const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return "";
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      auto &&_sv = *a1;
      if (std::holds_alternative<typename List<T1>::Nil>(_sv.v())) {
        return sep + p(a0);
      } else {
        return sep + p(a0) + intersperse<T1>(p, sep, *a1);
      }
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<std::string, F0 &, T1 &>
  static std::string list_to_string(F0 &&p, const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return "[]";
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      auto &&_sv = *a1;
      if (std::holds_alternative<typename List<T1>::Nil>(_sv.v())) {
        return "["s + p(a0) + "]"s;
      } else {
        return "["s + p(a0) + intersperse<T1>(p, "; ", *a1) + "]"s;
      }
    }
  }
};

struct Tokenizer {
  static std::pair<std::optional<std::basic_string_view<char>>,
                   std::basic_string_view<char>>
  next_token(std::basic_string_view<char> input,
             std::basic_string_view<char> soft,
             std::basic_string_view<char> hard);
  static List<std::basic_string_view<char>>
  list_tokens(std::basic_string_view<char> input,
              std::basic_string_view<char> soft,
              std::basic_string_view<char> hard);

  template <typename T1>
  static std::vector<T1> list_to_vec_h(const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return {};
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      std::vector<T1> v = list_to_vec_h<T1>(*a1);
      v.push_back(a0);
      return v;
    }
  }

  template <typename T1> static std::vector<T1> list_to_vec(const List<T1> &l) {
    return list_to_vec_h<T1>(l.rev());
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static std::vector<T2> list_to_vec_map_h(F0 &&f, const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return {};
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      std::vector<T2> v = list_to_vec_map_h<T1, T2>(f, *a1);
      v.push_back(f(a0));
      return v;
    }
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static std::vector<T2> list_to_vec_map(F0 &&f, const List<T1> &l) {
    return list_to_vec_map_h<T1, T2>(f, l.rev());
  }
};

#endif // INCLUDED_TOKENIZER
