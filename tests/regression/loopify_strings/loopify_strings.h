#ifndef INCLUDED_LOOPIFY_STRINGS
#define INCLUDED_LOOPIFY_STRINGS

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

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

struct LoopifyStrings {
  static std::shared_ptr<List<unsigned int>>
  append(const std::shared_ptr<List<unsigned int>> &l1,
         std::shared_ptr<List<unsigned int>> l2);
  static std::shared_ptr<List<unsigned int>>
  join_with(const unsigned int sep,
            const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<unsigned int>>
  repeat_string(const std::shared_ptr<List<unsigned int>> &s,
                const unsigned int n);
  static std::shared_ptr<List<unsigned int>>
  repeat_with_sep(std::shared_ptr<List<unsigned int>> s,
                  const std::shared_ptr<List<unsigned int>> &sep,
                  const unsigned int n);
  static std::shared_ptr<List<unsigned int>> string_chain_fuel(
      const unsigned int fuel, const std::shared_ptr<List<unsigned int>> &s,
      const unsigned int n, const std::shared_ptr<List<unsigned int>> &sep,
      const std::shared_ptr<List<unsigned int>> &end_marker);
  static std::shared_ptr<List<unsigned int>>
  string_chain(const std::shared_ptr<List<unsigned int>> &s,
               const unsigned int n,
               const std::shared_ptr<List<unsigned int>> &sep,
               const std::shared_ptr<List<unsigned int>> &end_marker);
  static std::shared_ptr<List<unsigned int>>
  reverse(const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static bool
  list_eq(const std::shared_ptr<List<unsigned int>> &l1,
          const std::shared_ptr<List<unsigned int>> &l2);
  __attribute__((pure)) static bool
  is_palindrome(const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<unsigned int>>
  intersperse(const unsigned int sep,
              const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<unsigned int>> intercalate(
      const std::shared_ptr<List<unsigned int>> &sep,
      const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll);
  static std::shared_ptr<List<unsigned int>> replicate(const unsigned int n,
                                                       const unsigned int x);
  static std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
  run_length_aux(const unsigned int current, const unsigned int count,
                 const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
  run_length_encode(const std::shared_ptr<List<unsigned int>> &l);
};

#endif // INCLUDED_LOOPIFY_STRINGS
