#ifndef INCLUDED_LOOPIFY_LIST_WINDOWS
#define INCLUDED_LOOPIFY_LIST_WINDOWS

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

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

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct LoopifyListWindows {
  __attribute__((pure)) static unsigned int
  len(const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  map_cons_helper(
      const unsigned int x,
      const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll);
  static std::shared_ptr<List<unsigned int>>
  drop(const unsigned int m, std::shared_ptr<List<unsigned int>> xs);
  __attribute__((pure)) static std::pair<std::shared_ptr<List<unsigned int>>,
                                         std::shared_ptr<List<unsigned int>>>
  span_eq(const unsigned int first, std::shared_ptr<List<unsigned int>> lst);
  static std::shared_ptr<List<unsigned int>>
  differences(const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
  sliding_pairs(const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  inits(const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  tails(std::shared_ptr<List<unsigned int>> l);
  static std::shared_ptr<List<unsigned int>>
  take(const unsigned int n, const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  windows_fuel(const unsigned int fuel, const unsigned int n,
               const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  windows(const unsigned int n, const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  chunks_fuel(const unsigned int fuel, const unsigned int n,
              const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  chunks(const unsigned int n, const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  group_fuel(const unsigned int fuel,
             const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  group(const std::shared_ptr<List<unsigned int>> &l);
};

#endif // INCLUDED_LOOPIFY_LIST_WINDOWS
