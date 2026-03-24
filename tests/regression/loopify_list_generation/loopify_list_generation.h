#ifndef INCLUDED_LOOPIFY_LIST_GENERATION
#define INCLUDED_LOOPIFY_LIST_GENERATION

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<t_A>> Nil_() {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::shared_ptr<List<t_A>>
    Cons_(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }

    static std::unique_ptr<List<t_A>> Nil_uptr() {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::unique_ptr<List<t_A>>
    Cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  std::shared_ptr<List<t_A>> app(std::shared_ptr<List<t_A>> m) const {
    std::shared_ptr<List<t_A>> _head{};
    std::shared_ptr<List<t_A>> _last{};
    const List *_loop_self = this;
    std::shared_ptr<List<t_A>> _loop_m = m;
    bool _continue = true;
    while (_continue) {
      std::visit(
          Overloaded{
              [&](const typename List<t_A>::Nil _args) {
                if (_last) {
                  std::get<typename List<t_A>::Cons>(_last->v_mut()).d_a1 =
                      _loop_m;
                } else {
                  _head = _loop_m;
                }
                _continue = false;
              },
              [&](const typename List<t_A>::Cons _args) {
                auto _cell = List<t_A>::ctor::Cons_(_args.d_a0, nullptr);
                if (_last) {
                  std::get<typename List<t_A>::Cons>(_last->v_mut()).d_a1 =
                      _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                List *_next_self = _loop_m.get();
                std::shared_ptr<List<t_A>> _next_m = _args.d_a1;
                _loop_self = std::move(_next_self);
                _loop_m = std::move(_next_m);
              }},
          _loop_self->v());
    }
    return _head;
  }
};

struct LoopifyListGeneration {
  static std::shared_ptr<List<unsigned int>> replicate(const unsigned int n,
                                                       const unsigned int x);
  static std::shared_ptr<List<unsigned int>>
  stutter(const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<unsigned int>>
  cycle(const unsigned int n, const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<unsigned int>> iterate(const unsigned int n,
                                                     const unsigned int x);
  static std::shared_ptr<List<unsigned int>> replicate_list(
      const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> &l);
  static std::shared_ptr<List<unsigned int>>
  repeat_with_sep(const unsigned int sep, const unsigned int n,
                  const unsigned int x);
  static std::shared_ptr<List<unsigned int>> range(const unsigned int start,
                                                   const unsigned int len);
};

#endif // INCLUDED_LOOPIFY_LIST_GENERATION
