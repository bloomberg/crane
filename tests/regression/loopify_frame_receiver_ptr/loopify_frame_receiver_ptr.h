#ifndef INCLUDED_LOOPIFY_FRAME_RECEIVER_PTR
#define INCLUDED_LOOPIFY_FRAME_RECEIVER_PTR

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <utility>
#include <variant>

template <typename A> struct List;
struct Ascii;
struct String;

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

  template <typename _U> List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    crane::small_vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        std::atomic_thread_fence(std::memory_order_acquire);
        _drain(_cur->v_mut());
      }
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Ascii {
  // DATA
  bool a0;
  bool a1;
  bool a2;
  bool a3;
  bool a4;
  bool a5;
  bool a6;
  bool a7;

  // ACCESSORS
  Ascii clone() const { return {a0, a1, a2, a3, a4, a5, a6, a7}; }

  // CREATORS
  static Ascii ascii0(bool a0, bool a1, bool a2, bool a3, bool a4, bool a5,
                      bool a6, bool a7) {
    return {a0, a1, a2, a3, a4, a5, a6, a7};
  }
};

struct String {
  // TYPES
  struct EmptyString {};

  struct String0 {
    Ascii a0;
    std::shared_ptr<String> a1;
  };

  using variant_t = std::variant<EmptyString, String0>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  String() {}

  explicit String(EmptyString _v) : v_(_v) {}

  explicit String(String0 _v) : v_(std::move(_v)) {}

  static String emptystring() { return String(EmptyString{}); }

  static String string0(Ascii a0, String a1) {
    return String(
        String0{std::move(a0), std::make_shared<String>(std::move(a1))});
  }

  // MANIPULATORS
  ~String() {
    crane::small_vector<std::shared_ptr<String>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<String0>(&_v)) {
        if (_alt->a1) {
          _stack.push_back(std::move(_alt->a1));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        std::atomic_thread_fence(std::memory_order_acquire);
        _drain(_cur->v_mut());
      }
    }
  }

  String(const String &) = default;
  String &operator=(const String &) = default;
  String(String &&) noexcept = default;
  String &operator=(String &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  String append(String s2) const {
    std::shared_ptr<String> _head{};
    std::shared_ptr<String> *_write = &_head;
    const String *_loop_self = this;
    String _loop_s2 = std::move(s2);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename String::EmptyString>(_sv.v())) {
        *_write = std::make_shared<String>(std::move(_loop_s2));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename String::String0>(_sv.v());
        auto _cell =
            std::make_shared<String>(typename String::String0(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename String::String0>((*_write)->v_mut()).a1;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_head);
  }

  String concat(const List<String> &ls) const {
    const String *_self = this;

    /// _Enter: captures varying parameters for each recursive call.
    struct _Enter {
      const String *_self;
      const List<String> *ls;
    };

    /// _Resume_Cons: saves [a0, _self], resumes after recursive call with
    /// _result.
    struct _Resume_Cons {
      String a0;
      String _self;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    String _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{_self, &ls});
    /// Loopified concat: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const String *_self = _f._self;
        const List<String> &ls = *_f.ls;
        if (std::holds_alternative<typename List<String>::Nil>(ls.v())) {
          _result = String::emptystring();
        } else {
          const auto &[a0, a1] = std::get<typename List<String>::Cons>(ls.v());
          auto &&_sv = *a1;
          if (std::holds_alternative<typename List<String>::Nil>(_sv.v())) {
            _result = std::move(a0);
          } else {
            _stack.emplace_back(_Resume_Cons{a0, *_self});
            _stack.emplace_back(_Enter{crane_raw(_self), crane_raw(a1)});
          }
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = std::move(_f.a0).append(
            std::move(_f._self).append(std::move(_result)));
      }
    }
    return _result;
  }
};

struct LoopifyFrameReceiverPtr {
  static String f(const List<String> &l);
};

#endif // INCLUDED_LOOPIFY_FRAME_RECEIVER_PTR
