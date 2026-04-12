#ifndef INCLUDED_LOOPIFY_LIST_RELATIONS
#define INCLUDED_LOOPIFY_LIST_RELATIONS

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
                        [&](const typename List<t_A>::Nil) -> void {
                          _result = 0u;
                        },
                        [&](const typename List<t_A>::Cons _args) -> void {
                          _stack.push_back(_Call1{});
                          _stack.push_back(_Enter{_args.d_a1.get()});
                        }},
                    _self->v());
              },
              [&](_Call1) { _result = (_result + 1); }},
          _frame);
    }
    return _result;
  }
};

struct LoopifyListRelations {
  __attribute__((pure)) static bool
  is_prefix_of(const std::shared_ptr<List<unsigned int>> &l1,
               const std::shared_ptr<List<unsigned int>> &l2);
  __attribute__((pure)) static bool
  is_suffix_of(const std::shared_ptr<List<unsigned int>> &l1,
               const std::shared_ptr<List<unsigned int>> &l2);
  __attribute__((pure)) static bool
  is_infix_of_aux(const std::shared_ptr<List<unsigned int>> &needle,
                  const std::shared_ptr<List<unsigned int>> &haystack);
  __attribute__((pure)) static bool
  is_infix_of(const std::shared_ptr<List<unsigned int>> &_x0,
              const std::shared_ptr<List<unsigned int>> &_x1);
  static std::shared_ptr<List<unsigned int>>
  find_sublists_aux(const std::shared_ptr<List<unsigned int>> &needle,
                    const std::shared_ptr<List<unsigned int>> &haystack,
                    const unsigned int idx);
  static std::shared_ptr<List<unsigned int>>
  find_sublists(const std::shared_ptr<List<unsigned int>> &needle,
                const std::shared_ptr<List<unsigned int>> &haystack);
  __attribute__((pure)) static bool
  list_eq(const std::shared_ptr<List<unsigned int>> &l1,
          const std::shared_ptr<List<unsigned int>> &l2);
  __attribute__((pure)) static unsigned int
  list_compare(const std::shared_ptr<List<unsigned int>> &l1,
               const std::shared_ptr<List<unsigned int>> &l2);
  static std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
  zip(const std::shared_ptr<List<unsigned int>> &l1,
      const std::shared_ptr<List<unsigned int>> &l2);
  static std::shared_ptr<
      List<std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>
  zip3(const std::shared_ptr<List<unsigned int>> &l1,
       const std::shared_ptr<List<unsigned int>> &l2,
       const std::shared_ptr<List<unsigned int>> &l3);
  static std::shared_ptr<List<unsigned int>>
  interleave(std::shared_ptr<List<unsigned int>> l1,
             std::shared_ptr<List<unsigned int>> l2);
  static std::shared_ptr<List<unsigned int>>
  merge_fuel(const unsigned int fuel, std::shared_ptr<List<unsigned int>> l1,
             std::shared_ptr<List<unsigned int>> l2);
  static std::shared_ptr<List<unsigned int>>
  merge(const std::shared_ptr<List<unsigned int>> &l1,
        const std::shared_ptr<List<unsigned int>> &l2);
  static std::shared_ptr<List<unsigned int>>
  union_(const std::shared_ptr<List<unsigned int>> &l1,
         std::shared_ptr<List<unsigned int>> l2);
  static std::shared_ptr<List<unsigned int>>
  intersection(const std::shared_ptr<List<unsigned int>> &l1,
               const std::shared_ptr<List<unsigned int>> &l2);
};

#endif // INCLUDED_LOOPIFY_LIST_RELATIONS
