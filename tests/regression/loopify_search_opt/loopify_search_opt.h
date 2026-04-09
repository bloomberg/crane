#ifndef INCLUDED_LOOPIFY_SEARCH_OPT
#define INCLUDED_LOOPIFY_SEARCH_OPT

#include <algorithm>
#include <functional>
#include <memory>
#include <type_traits>
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

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

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

  __attribute__((pure)) unsigned int length() const {
    const List *_self = this;

    struct _Enter {
      const List *_self;
    };

    struct _Call1 {};

    using _Frame = std::variant<_Enter, _Call1>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{_self});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const List *_self = _f._self;
                std::visit(
                    Overloaded{
                        [&](const typename List<t_A>::Nil _args) -> void {
                          _result = 0u;
                        },
                        [&](const typename List<t_A>::Cons _args) -> void {
                          _stack.push_back(_Call1{});
                          _stack.push_back(_Enter{_args.d_a1.get()});
                        }},
                    _self->v());
              },
              [&](_Call1 _f) { _result = (_result + 1); }},
          _frame);
    }
    return _result;
  }
};

struct LoopifySearchOpt {
  static std::shared_ptr<List<unsigned int>>
  lis(const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<unsigned int>>
  longest_run_fuel(const unsigned int fuel,
                   std::shared_ptr<List<unsigned int>> current,
                   std::shared_ptr<List<unsigned int>> best,
                   const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<unsigned int>>
  longest_run(const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static unsigned int knapsack_fuel(
      const unsigned int fuel, const unsigned int capacity,
      const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
          &items);
  __attribute__((pure)) static unsigned int
  knapsack(const unsigned int capacity,
           const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
               &items);
  __attribute__((pure)) static bool
  subset_sum_fuel(const unsigned int fuel, const unsigned int target,
                  const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static bool
  subset_sum(const unsigned int target,
             const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  majority(const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static bool
  binary_search_fuel(const unsigned int fuel, const unsigned int target,
                     const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static bool
  binary_search(const unsigned int target,
                const std::shared_ptr<List<unsigned int>> &l);
};

#endif // INCLUDED_LOOPIFY_SEARCH_OPT
