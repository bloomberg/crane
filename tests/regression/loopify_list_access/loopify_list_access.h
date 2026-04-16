#ifndef INCLUDED_LOOPIFY_LIST_ACCESS
#define INCLUDED_LOOPIFY_LIST_ACCESS

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

struct LoopifyListAccess {
  __attribute__((pure)) static unsigned int
  nth(const unsigned int n, const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static unsigned int
  last(const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static unsigned int
  index_of_aux(const unsigned int x,
               const std::shared_ptr<List<unsigned int>> &l,
               const unsigned int idx);
  __attribute__((pure)) static unsigned int
  index_of(const unsigned int x, const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static bool
  member(const unsigned int x, const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static unsigned int
  lookup(const unsigned int key,
         const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> &l);
  static std::shared_ptr<List<unsigned int>> lookup_all(
      const unsigned int key,
      const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> &l);

  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  find(F0 &&p, const std::shared_ptr<List<unsigned int>> &l) {
    unsigned int _result;
    std::shared_ptr<List<unsigned int>> _loop_l = l;
    bool _continue = true;
    while (_continue) {
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l->v())) {
        _result = 0u;
        _continue = false;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l->v());
        if (p(d_a0)) {
          _result = d_a0;
          _continue = false;
        } else {
          _loop_l = d_a1;
        }
      }
    }
    return _result;
  }

  __attribute__((pure)) static unsigned int
  count(const unsigned int x, const std::shared_ptr<List<unsigned int>> &l);

  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  count_matching(F0 &&p, const std::shared_ptr<List<unsigned int>> &l) {
    struct _Enter {
      const std::shared_ptr<List<unsigned int>> l;
    };

    struct _Call1 {
      decltype(1u) _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        const auto &_f = std::get<_Enter>(_frame);
        const std::shared_ptr<List<unsigned int>> l = _f.l;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
          _result = 0u;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l->v());
          if (p(d_a0)) {
            _stack.emplace_back(_Call1{1u});
            _stack.emplace_back(_Enter{d_a1});
          } else {
            _stack.emplace_back(_Enter{d_a1});
          }
        }
      } else {
        const auto &_f = std::get<_Call1>(_frame);
        _result = (_f._s0 + _result);
      }
    }
    return _result;
  }

  __attribute__((pure)) static bool
  elem_at_eq(const unsigned int idx, const unsigned int val,
             const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static unsigned int
  nth_default(const unsigned int n, const unsigned int default0,
              const std::shared_ptr<List<unsigned int>> &l);
};

#endif // INCLUDED_LOOPIFY_LIST_ACCESS
