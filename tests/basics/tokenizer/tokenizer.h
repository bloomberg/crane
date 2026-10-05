#ifndef INCLUDED_TOKENIZER
#define INCLUDED_TOKENIZER

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
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

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
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
  List(List &&) = default;
  List &operator=(List &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  List<A> rev() const {
    const List<A> *_self = this;

    /// CraneEnter: captures varying parameters for each recursive call.
    struct CraneEnter {
      const List<A> *_self;
    };

    /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_Cons {
      A a0;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    List<A> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{_self});
    /// Loopified rev: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = List<A>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(CraneCont_Cons{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        auto a0 = std::move(_f.a0);
        _result = std::move(_result).app(List<A>::cons(a0, List<A>::nil()));
      }
    }
    return _result;
  }

  List<A> app(List<A> m) const {
    std::optional<List<A>> _root{};
    std::shared_ptr<List<A>> *_write = nullptr;
    const List<A> *_loop_self = this;
    List<A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = std::move(_loop_m);
        (_write ? *(*_write = std::make_shared<List<A>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell = typename List<A>::Cons(a0, nullptr);
        List<A> &_node =
            (_write ? *(*_write = std::make_shared<List<A>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<A>::Cons>(_node.v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }
};

struct ToString {
  template <typename T1, typename T2, typename F0, typename F1>
  static std::string pair_to_string(F0 &&p1, F1 &&p2,
                                    const std::pair<T1, T2> &x) {
    const auto &[a, b] = x;
    return std::string("(") + p1(a) + std::string(", ") + p2(b) +
           std::string(")");
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<std::string, F0 &, const T1 &>
  static std::string intersperse(F0 &&p, std::string sep, const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return "";
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      auto &&_sv = *a1;
      if (std::holds_alternative<typename List<T1>::Nil>(_sv.v())) {
        return std::move(sep) + p(a0);
      } else {
        return sep + p(a0) + intersperse<T1>(p, sep, *a1);
      }
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<std::string, F0 &, const T1 &>
  static std::string list_to_string(F0 &&p, const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return "[]";
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      auto &&_sv = *a1;
      if (std::holds_alternative<typename List<T1>::Nil>(_sv.v())) {
        return std::string("[") + p(a0) + std::string("]");
      } else {
        return std::string("[") + p(a0) + intersperse<T1>(p, "; ", *a1) +
               std::string("]");
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
    requires std::is_invocable_r_v<T2, F0 &, const T1 &>
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
  static std::vector<T2> list_to_vec_map(F0 &&f, const List<T1> &l) {
    return list_to_vec_map_h<T1, T2>(f, l.rev());
  }
};

#endif // INCLUDED_TOKENIZER
