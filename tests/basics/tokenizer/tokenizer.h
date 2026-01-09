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
  template <typename A> struct nil;
  template <typename A> struct cons;
  template <typename A> using list = std::variant<nil<A>, cons<A>>;
  template <typename A> struct nil {
    static std::shared_ptr<list<A>> make() {
      return std::make_shared<list<A>>(nil<A>{});
    }
  };
  template <typename A> struct cons {
    A _a0;
    std::shared_ptr<list<A>> _a1;
    static std::shared_ptr<list<A>> make(A _a0, std::shared_ptr<list<A>> _a1) {
      return std::make_shared<list<A>>(cons<A>{_a0, _a1});
    }
  };
};

template <typename T1>
std::shared_ptr<typename List::list<T1>>
app(const std::shared_ptr<typename List::list<T1>> l,
    const std::shared_ptr<typename List::list<T1>> m) {
  return std::visit(
      Overloaded{[&](const typename List::nil<T1> _args)
                     -> std::shared_ptr<typename List::list<T1>> { return m; },
                 [&](const typename List::cons<T1> _args)
                     -> std::shared_ptr<typename List::list<T1>> {
                   T1 a = _args._a0;
                   std::shared_ptr<typename List::list<T1>> l1 = _args._a1;
                   return List::cons<T1>::make(a, app<T1>(l1, m));
                 }},
      *l);
}

template <typename T1>
std::shared_ptr<typename List::list<T1>>
rev(const std::shared_ptr<typename List::list<T1>> l) {
  return std::visit(
      Overloaded{[&](const typename List::nil<T1> _args)
                     -> std::shared_ptr<typename List::list<T1>> {
                   return List::nil<T1>::make();
                 },
                 [&](const typename List::cons<T1> _args)
                     -> std::shared_ptr<typename List::list<T1>> {
                   T1 x = _args._a0;
                   std::shared_ptr<typename List::list<T1>> l_ = _args._a1;
                   return app<T1>(rev<T1>(l_), List::cons<T1>::make(
                                                   x, List::nil<T1>::make()));
                 }},
      *l);
}

struct ToString {
  template <typename T1, typename T2, MapsTo<std::string, T1> F0,
            MapsTo<std::string, T2> F1>
  std::string pair_to_string(F0 &&p1, F1 &&p2, const std::pair<T1, T2> x) {
    T1 a = x.first;
    T2 b = x.second;
    return "(" + p1(a) + ", " + p2(b) + ")";
  }

  template <typename T1, MapsTo<std::string, T1> F0>
  std::string intersperse(F0 &&p, const std::string sep,
                          const std::shared_ptr<typename List::list<T1>> l) {
    return std::visit(
        Overloaded{
            [&](const typename List::nil<T1> _args) -> std::string {
              return "";
            },
            [&](const typename List::cons<T1> _args) -> std::string {
              T1 z = _args._a0;
              std::shared_ptr<typename List::list<T1>> l_ = _args._a1;
              return std::visit(
                  Overloaded{
                      [&](const typename List::nil<T1> _args) -> std::string {
                        return sep + p(z);
                      },
                      [&](const typename List::cons<T1> _args) -> std::string {
                        return sep + p(z) + intersperse<T1>(p, sep, l_);
                      }},
                  *l_);
            }},
        *l);
  }

  template <typename T1, MapsTo<std::string, T1> F0>
  std::string list_to_string(F0 &&p,
                             const std::shared_ptr<typename List::list<T1>> l) {
    return std::visit(
        Overloaded{
            [&](const typename List::nil<T1> _args) -> std::string {
              return "[]";
            },
            [&](const typename List::cons<T1> _args) -> std::string {
              T1 y = _args._a0;
              std::shared_ptr<typename List::list<T1>> l_ = _args._a1;
              return std::visit(
                  Overloaded{
                      [&](const typename List::nil<T1> _args) -> std::string {
                        return "[" + p(y) + "]";
                      },
                      [&](const typename List::cons<T1> _args) -> std::string {
                        return "[" + p(y) + intersperse<T1>(p, "; ", l_) + "]";
                      }},
                  *l_);
            }},
        *l);
  }
};

struct Tokenizer {
  static std::pair<std::optional<std::basic_string_view<char>>,
                   std::basic_string_view<char>>
  next_token(const std::basic_string_view<char> input,
             const std::basic_string_view<char> soft,
             const std::basic_string_view<char> hard);

  static std::shared_ptr<typename List::list<std::basic_string_view<char>>>
  list_tokens(const std::basic_string_view<char> input,
              const std::basic_string_view<char> soft,
              const std::basic_string_view<char> hard);

  template <typename T1>
  std::vector<T1>
  list_to_vec_h(const std::shared_ptr<typename List::list<T1>> l) {
    return std::visit(
        Overloaded{[&](const typename List::nil<T1> _args) -> std::vector<T1> {
                     return {};
                   },
                   [&](const typename List::cons<T1> _args) -> std::vector<T1> {
                     T1 a = _args._a0;
                     std::shared_ptr<typename List::list<T1>> l_ = _args._a1;
                     std::vector<T1> v = list_to_vec_h<T1>(l_);
                     v.push_back(a);
                     return v;
                   }},
        *l);
  }

  template <typename T1>
  std::vector<T1>
  list_to_vec(const std::shared_ptr<typename List::list<T1>> l) {
    return list_to_vec_h<T1>(rev<T1>(l));
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  std::vector<T2>
  list_to_vec_map_h(F0 &&f, const std::shared_ptr<typename List::list<T1>> l) {
    return std::visit(
        Overloaded{[&](const typename List::nil<T1> _args) -> std::vector<T2> {
                     return {};
                   },
                   [&](const typename List::cons<T1> _args) -> std::vector<T2> {
                     T1 a = _args._a0;
                     std::shared_ptr<typename List::list<T1>> l_ = _args._a1;
                     std::vector<T2> v = list_to_vec_map_h<T1, T2>(f, l_);
                     v.push_back(f(a));
                     return v;
                   }},
        *l);
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  std::vector<T2>
  list_to_vec_map(F0 &&f, const std::shared_ptr<typename List::list<T1>> l) {
    return list_to_vec_map_h<T1, T2>(f, rev<T1>(l));
  }
};
