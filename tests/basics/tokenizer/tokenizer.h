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

  std::shared_ptr<List<t_A>> rev() const {
    return std::visit(
        Overloaded{[](const typename List<t_A>::Nil _args)
                       -> std::shared_ptr<List<t_A>> {
                     return List<t_A>::ctor::Nil_();
                   },
                   [](const typename List<t_A>::Cons _args)
                       -> std::shared_ptr<List<t_A>> {
                     t_A x = _args.d_a0;
                     std::shared_ptr<List<t_A>> l_ = _args.d_a1;
                     return std::move(l_)->rev()->app(
                         List<t_A>::ctor::Cons_(x, List<t_A>::ctor::Nil_()));
                   }},
        this->v());
  }

  std::shared_ptr<List<t_A>> app(std::shared_ptr<List<t_A>> m) const {
    return std::visit(
        Overloaded{[&](const typename List<t_A>::Nil _args)
                       -> std::shared_ptr<List<t_A>> { return m; },
                   [&](const typename List<t_A>::Cons _args)
                       -> std::shared_ptr<List<t_A>> {
                     t_A a = _args.d_a0;
                     std::shared_ptr<List<t_A>> l1 = _args.d_a1;
                     return List<t_A>::ctor::Cons_(a, std::move(l1)->app(m));
                   }},
        this->v());
  }
};

struct ToString {
  template <typename T1, typename T2, MapsTo<std::string, T1> F0,
            MapsTo<std::string, T2> F1>
  __attribute__((pure)) static std::string
  pair_to_string(F0 &&p1, F1 &&p2, const std::pair<T1, T2> x) {
    T1 a = x.first;
    T2 b = x.second;
    return "("s + p1(a) + ", "s + p2(b) + ")"s;
  }

  template <typename T1, MapsTo<std::string, T1> F0>
  __attribute__((pure)) static std::string
  intersperse(F0 &&p, const std::string sep,
              const std::shared_ptr<List<T1>> &l) {
    return std::visit(
        Overloaded{
            [](const typename List<T1>::Nil _args) -> std::string {
              return "";
            },
            [&](const typename List<T1>::Cons _args) -> std::string {
              T1 z = _args.d_a0;
              std::shared_ptr<List<T1>> l_ = _args.d_a1;
              return std::visit(
                  Overloaded{
                      [&](const typename List<T1>::Nil _args) -> std::string {
                        return sep + p(z);
                      },
                      [&](const typename List<T1>::Cons _args) -> std::string {
                        return sep + p(z) +
                               intersperse<T1>(p, sep, std::move(l_));
                      }},
                  l_->v());
            }},
        l->v());
  }

  template <typename T1, MapsTo<std::string, T1> F0>
  __attribute__((pure)) static std::string
  list_to_string(F0 &&p, const std::shared_ptr<List<T1>> &l) {
    return std::visit(
        Overloaded{
            [](const typename List<T1>::Nil _args) -> std::string {
              return "[]";
            },
            [&](const typename List<T1>::Cons _args) -> std::string {
              T1 y = _args.d_a0;
              std::shared_ptr<List<T1>> l_ = _args.d_a1;
              return std::visit(
                  Overloaded{
                      [&](const typename List<T1>::Nil _args) -> std::string {
                        return "["s + p(y) + "]"s;
                      },
                      [&](const typename List<T1>::Cons _args) -> std::string {
                        return "["s + p(y) +
                               intersperse<T1>(p, "; ", std::move(l_)) + "]"s;
                      }},
                  l_->v());
            }},
        l->v());
  }
};

struct Tokenizer {
  __attribute__((pure)) static std::pair<
      std::optional<std::basic_string_view<char>>, std::basic_string_view<char>>
  next_token(const std::basic_string_view<char> input,
             const std::basic_string_view<char> soft,
             const std::basic_string_view<char> hard);
  static std::shared_ptr<List<std::basic_string_view<char>>>
  list_tokens(const std::basic_string_view<char> input,
              const std::basic_string_view<char> soft,
              const std::basic_string_view<char> hard);

  template <typename T1>
  __attribute__((pure)) static std::vector<T1>
  list_to_vec_h(const std::shared_ptr<List<T1>> &l) {
    return std::visit(
        Overloaded{[](const typename List<T1>::Nil _args) -> std::vector<T1> {
                     return {};
                   },
                   [](const typename List<T1>::Cons _args) -> std::vector<T1> {
                     T1 a = _args.d_a0;
                     std::shared_ptr<List<T1>> l_ = _args.d_a1;
                     std::vector<T1> v = list_to_vec_h<T1>(l_);
                     v.push_back(a);
                     return v;
                   }},
        l->v());
  }

  template <typename T1>
  __attribute__((pure)) static std::vector<T1>
  list_to_vec(const std::shared_ptr<List<T1>> &l) {
    return list_to_vec_h<T1>(l->rev());
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  __attribute__((pure)) static std::vector<T2>
  list_to_vec_map_h(F0 &&f, const std::shared_ptr<List<T1>> &l) {
    return std::visit(
        Overloaded{[](const typename List<T1>::Nil _args) -> std::vector<T2> {
                     return {};
                   },
                   [&](const typename List<T1>::Cons _args) -> std::vector<T2> {
                     T1 a = _args.d_a0;
                     std::shared_ptr<List<T1>> l_ = _args.d_a1;
                     std::vector<T2> v = list_to_vec_map_h<T1, T2>(f, l_);
                     v.push_back(f(a));
                     return v;
                   }},
        l->v());
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  __attribute__((pure)) static std::vector<T2>
  list_to_vec_map(F0 &&f, const std::shared_ptr<List<T1>> &l) {
    return list_to_vec_map_h<T1, T2>(f, l->rev());
  }
};

#endif // INCLUDED_TOKENIZER
