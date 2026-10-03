#ifndef INCLUDED_TOKENIZER
#define INCLUDED_TOKENIZER

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <string_view>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

using namespace std::string_literals;

template <typename A> struct List;

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

  template <typename _U>
  List(const List<_U> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const _U &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  List<A> rev() const {
    const List<A> *_self = this;

    /// _Enter: captures varying parameters for each recursive call.
    struct _Enter {
      const List<A> *_self;
    };

    /// _Cont_Cons: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct _Cont_Cons {
      A a0;
    };

    using _Frame = std::variant<_Enter, _Cont_Cons>;
    List<A> _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{_self});
    /// Loopified rev: _Enter -> _Cont_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = List<A>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_Cont_Cons{a0});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_Cont_Cons>(_frame));
        auto a0 = std::move(_f.a0);
        List<A> r_ = std::move(_result);
        _result = std::move(r_).app(List<A>::cons(a0, List<A>::nil()));
      }
    }
    return _result;
  }

  List<A> app(List<A> m) const {
    std::shared_ptr<List<A>> _head{};
    std::shared_ptr<List<A>> *_write = &_head;
    const List<A> *_loop_self = this;
    List<A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        *_write = std::make_shared<List<A>>(std::move(_loop_m));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell =
            std::make_shared<List<A>>(typename List<A>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<A>::Cons>((*_write)->v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_head);
  }
};

struct ToString {
  template <typename T1, typename T2, typename F0, typename F1>
    requires std::is_invocable_r_v<std::string, F0 &, T1 &> &&
             std::is_invocable_r_v<std::string, F1 &, T2 &>
  static std::string pair_to_string(F0 &&p1, F1 &&p2,
                                    const std::pair<T1, T2> &x) {
    const auto &[a, b] = x;
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

  template <typename T1, typename T2>
  static std::vector<T2>
  list_to_vec_map_h(std::type_identity_t<crane::fn<T2(T1)>> f,
                    const List<T1> &l) {
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
