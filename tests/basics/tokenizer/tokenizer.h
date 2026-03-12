#ifndef INCLUDED_TOKENIZER
#define INCLUDED_TOKENIZER

#include <algorithm>
#include <any>
#include <cassert>
#include <cstdint>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <string_view>
#include <utility>
#include <variant>
#include <vector>

using namespace std::string_literals;
template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename A> struct List {
  // TYPES
  struct nil {};

  struct cons {
    A _a0;
    std::shared_ptr<List<A>> _a1;
  };

  using variant_t = std::variant<nil, cons>;

private:
  // DATA
  variant_t v_;

  // CREATORS
  explicit List(nil _v) : v_(std::move(_v)) {}

  explicit List(cons _v) : v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<A>> nil_() {
      return std::shared_ptr<List<A>>(new List<A>(nil{}));
    }

    static std::shared_ptr<List<A>> cons_(A a0,
                                          const std::shared_ptr<List<A>> &a1) {
      return std::shared_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }

    static std::unique_ptr<List<A>> nil_uptr() {
      return std::unique_ptr<List<A>>(new List<A>(nil{}));
    }

    static std::unique_ptr<List<A>>
    cons_uptr(A a0, const std::shared_ptr<List<A>> &a1) {
      return std::unique_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
  };

  // MANIPULATORS
  variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  std::shared_ptr<List<A>> rev() const {
    return std::visit(
        Overloaded{
            [](const typename List<A>::nil _args) -> std::shared_ptr<List<A>> {
              return List<A>::ctor::nil_();
            },
            [](const typename List<A>::cons _args) -> std::shared_ptr<List<A>> {
              A x = _args._a0;
              std::shared_ptr<List<A>> l_ = _args._a1;
              return std::move(l_)->rev()->app(
                  List<A>::ctor::cons_(x, List<A>::ctor::nil_()));
            }},
        this->v());
  }

  std::shared_ptr<List<A>> app(std::shared_ptr<List<A>> m) const {
    return std::visit(Overloaded{[&](const typename List<A>::nil _args)
                                     -> std::shared_ptr<List<A>> { return m; },
                                 [&](const typename List<A>::cons _args)
                                     -> std::shared_ptr<List<A>> {
                                   A a = _args._a0;
                                   std::shared_ptr<List<A>> l1 = _args._a1;
                                   return List<A>::ctor::cons_(
                                       a, std::move(l1)->app(m));
                                 }},
                      this->v());
  }
};

struct ToString {
  template <typename T1, typename T2, MapsTo<std::string, T1> F0,
            MapsTo<std::string, T2> F1>
  static std::string pair_to_string(F0 &&p1, F1 &&p2,
                                    const std::pair<T1, T2> x) {
    T1 a = x.first;
    T2 b = x.second;
    return "("s + p1(a) + ", "s + p2(b) + ")"s;
  }

  template <typename T1, MapsTo<std::string, T1> F0>
  static std::string intersperse(F0 &&p, const std::string sep,
                                 const std::shared_ptr<List<T1>> &l) {
    return std::visit(
        Overloaded{
            [](const typename List<T1>::nil _args) -> std::string {
              return "";
            },
            [&](const typename List<T1>::cons _args) -> std::string {
              T1 z = _args._a0;
              std::shared_ptr<List<T1>> l_ = _args._a1;
              return std::visit(
                  Overloaded{
                      [&](const typename List<T1>::nil _args) -> std::string {
                        return sep + p(z);
                      },
                      [&](const typename List<T1>::cons _args) -> std::string {
                        return sep + p(z) +
                               intersperse<T1>(p, sep, std::move(l_));
                      }},
                  l_->v());
            }},
        l->v());
  }

  template <typename T1, MapsTo<std::string, T1> F0>
  static std::string list_to_string(F0 &&p,
                                    const std::shared_ptr<List<T1>> &l) {
    return std::visit(
        Overloaded{
            [](const typename List<T1>::nil _args) -> std::string {
              return "[]";
            },
            [&](const typename List<T1>::cons _args) -> std::string {
              T1 y = _args._a0;
              std::shared_ptr<List<T1>> l_ = _args._a1;
              return std::visit(
                  Overloaded{
                      [&](const typename List<T1>::nil _args) -> std::string {
                        return "["s + p(y) + "]"s;
                      },
                      [&](const typename List<T1>::cons _args) -> std::string {
                        return "["s + p(y) +
                               intersperse<T1>(p, "; ", std::move(l_)) + "]"s;
                      }},
                  l_->v());
            }},
        l->v());
  }
};

struct Tokenizer {
  static std::pair<std::optional<std::basic_string_view<char>>,
                   std::basic_string_view<char>>
  next_token(const std::basic_string_view<char> input,
             const std::basic_string_view<char> soft,
             const std::basic_string_view<char> hard);
  static std::shared_ptr<List<std::basic_string_view<char>>>
  list_tokens(const std::basic_string_view<char> input,
              const std::basic_string_view<char> soft,
              const std::basic_string_view<char> hard);

  template <typename T1>
  static std::vector<T1> list_to_vec_h(const std::shared_ptr<List<T1>> &l) {
    return std::visit(
        Overloaded{[](const typename List<T1>::nil _args) -> std::vector<T1> {
                     return {};
                   },
                   [](const typename List<T1>::cons _args) -> std::vector<T1> {
                     T1 a = _args._a0;
                     std::shared_ptr<List<T1>> l_ = _args._a1;
                     std::vector<T1> v = list_to_vec_h<T1>(l_);
                     v.push_back(a);
                     return v;
                   }},
        l->v());
  }

  template <typename T1>
  static std::vector<T1> list_to_vec(const std::shared_ptr<List<T1>> &l) {
    return list_to_vec_h<T1>(l->rev());
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static std::vector<T2> list_to_vec_map_h(F0 &&f,
                                           const std::shared_ptr<List<T1>> &l) {
    return std::visit(
        Overloaded{[](const typename List<T1>::nil _args) -> std::vector<T2> {
                     return {};
                   },
                   [&](const typename List<T1>::cons _args) -> std::vector<T2> {
                     T1 a = _args._a0;
                     std::shared_ptr<List<T1>> l_ = _args._a1;
                     std::vector<T2> v = list_to_vec_map_h<T1, T2>(f, l_);
                     v.push_back(f(a));
                     return v;
                   }},
        l->v());
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static std::vector<T2> list_to_vec_map(F0 &&f,
                                         const std::shared_ptr<List<T1>> &l) {
    return list_to_vec_map_h<T1, T2>(f, l->rev());
  }
};

#endif // INCLUDED_TOKENIZER
