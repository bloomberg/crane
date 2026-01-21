#include <algorithm>
#include <fstream>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct List {
  template <typename A> struct list {
  public:
    struct nil {};
    struct cons {
      A _a0;
      std::shared_ptr<list<A>> _a1;
    };
    using variant_t = std::variant<nil, cons>;

  private:
    variant_t v_;
    explicit list(nil x) : v_(std::move(x)) {}
    explicit list(cons x) : v_(std::move(x)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<list<A>> nil_() {
        return std::shared_ptr<list<A>>(new list<A>(nil{}));
      }
      static std::shared_ptr<list<A>>
      cons_(A a0, const std::shared_ptr<list<A>> &a1) {
        return std::shared_ptr<list<A>>(new list<A>(cons{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
    std::shared_ptr<list<A>> app(const std::shared_ptr<list<A>> &m) const {
      return std::visit(
          Overloaded{[&](const typename List::list<A>::nil _args)
                         -> std::shared_ptr<List::list<A>> { return m; },
                     [&](const typename List::list<A>::cons _args)
                         -> std::shared_ptr<List::list<A>> {
                       A a = _args._a0;
                       std::shared_ptr<List::list<A>> l1 = _args._a1;
                       return List::list<A>::ctor::cons_(a, l1->app(m));
                     }},
          this->v());
    }
  };
};

template <typename T1>
std::shared_ptr<List::list<T1>> rev(const std::shared_ptr<List::list<T1>> &l) {
  return std::visit(Overloaded{[&](const typename List::list<T1>::nil _args)
                                   -> std::shared_ptr<List::list<T1>> {
                                 return List::list<T1>::ctor::nil_();
                               },
                               [&](const typename List::list<T1>::cons _args)
                                   -> std::shared_ptr<List::list<T1>> {
                                 T1 x = _args._a0;
                                 std::shared_ptr<List::list<T1>> l_ = _args._a1;
                                 return rev<T1>(l_)->app(
                                     List::list<T1>::ctor::cons_(
                                         x, List::list<T1>::ctor::nil_()));
                               }},
                    l->v());
}

struct ToString {
  template <typename T1, typename T2, MapsTo<std::string, T1> F0,
            MapsTo<std::string, T2> F1>
  static std::string pair_to_string(F0 &&p1, F1 &&p2,
                                    const std::pair<T1, T2> x) {
    T1 a = x.first;
    T2 b = x.second;
    return "(" + p1(a) + ", " + p2(b) + ")";
  }

  template <typename T1, MapsTo<std::string, T1> F0>
  static std::string intersperse(F0 &&p, const std::string sep,
                                 const std::shared_ptr<List::list<T1>> &l) {
    return std::visit(
        Overloaded{
            [&](const typename List::list<T1>::nil _args) -> std::string {
              return "";
            },
            [&](const typename List::list<T1>::cons _args) -> std::string {
              T1 z = _args._a0;
              std::shared_ptr<List::list<T1>> l_ = _args._a1;
              return std::visit(
                  Overloaded{[&](const typename List::list<T1>::nil _args)
                                 -> std::string { return sep + p(z); },
                             [&](const typename List::list<T1>::cons _args)
                                 -> std::string {
                               return sep + p(z) + intersperse<T1>(p, sep, l_);
                             }},
                  l_->v());
            }},
        l->v());
  }

  template <typename T1, MapsTo<std::string, T1> F0>
  static std::string list_to_string(F0 &&p,
                                    const std::shared_ptr<List::list<T1>> &l) {
    return std::visit(
        Overloaded{
            [&](const typename List::list<T1>::nil _args) -> std::string {
              return "[]";
            },
            [&](const typename List::list<T1>::cons _args) -> std::string {
              T1 y = _args._a0;
              std::shared_ptr<List::list<T1>> l_ = _args._a1;
              return std::visit(
                  Overloaded{[&](const typename List::list<T1>::nil _args)
                                 -> std::string { return "[" + p(y) + "]"; },
                             [&](const typename List::list<T1>::cons _args)
                                 -> std::string {
                               return "[" + p(y) +
                                      intersperse<T1>(p, "; ", l_) + "]";
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

  static std::shared_ptr<List::list<std::basic_string_view<char>>>
  list_tokens(const std::basic_string_view<char> input,
              const std::basic_string_view<char> soft,
              const std::basic_string_view<char> hard);

  template <typename T1>
  static std::vector<T1>
  list_to_vec_h(const std::shared_ptr<List::list<T1>> &l) {
    return std::visit(
        Overloaded{
            [&](const typename List::list<T1>::nil _args) -> std::vector<T1> {
              return {};
            },
            [&](const typename List::list<T1>::cons _args) -> std::vector<T1> {
              T1 a = _args._a0;
              std::shared_ptr<List::list<T1>> l_ = _args._a1;
              std::vector<T1> v = list_to_vec_h<T1>(l_);
              v.push_back(a);
              return v;
            }},
        l->v());
  }

  template <typename T1>
  static std::vector<T1> list_to_vec(const std::shared_ptr<List::list<T1>> &l) {
    return list_to_vec_h<T1>(rev<T1>(l));
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static std::vector<T2>
  list_to_vec_map_h(F0 &&f, const std::shared_ptr<List::list<T1>> &l) {
    return std::visit(
        Overloaded{
            [&](const typename List::list<T1>::nil _args) -> std::vector<T2> {
              return {};
            },
            [&](const typename List::list<T1>::cons _args) -> std::vector<T2> {
              T1 a = _args._a0;
              std::shared_ptr<List::list<T1>> l_ = _args._a1;
              std::vector<T2> v = list_to_vec_map_h<T1, T2>(f, l_);
              v.push_back(f(a));
              return v;
            }},
        l->v());
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static std::vector<T2>
  list_to_vec_map(F0 &&f, const std::shared_ptr<List::list<T1>> &l) {
    return list_to_vec_map_h<T1, T2>(f, rev<T1>(l));
  }
};
