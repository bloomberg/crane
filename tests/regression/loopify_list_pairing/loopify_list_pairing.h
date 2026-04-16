#ifndef INCLUDED_LOOPIFY_LIST_PAIRING
#define INCLUDED_LOOPIFY_LIST_PAIRING

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

  __attribute__((pure)) unsigned int length() const {
    const List *_self = this;

    struct _Enter {
      const List *_self;
    };

    struct _Call1 {};

    using _Frame = std::variant<_Enter, _Call1>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.emplace_back(_Enter{_self});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        const auto &_f = std::get<_Enter>(_frame);
        const List *_self = _f._self;
        if (std::holds_alternative<typename List<t_A>::Nil>(_self->v())) {
          _result = 0u;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<t_A>::Cons>(_self->v());
          _stack.emplace_back(_Call1{});
          _stack.emplace_back(_Enter{d_a1.get()});
        }
      } else {
        const auto &_f = std::get<_Call1>(_frame);
        _result = (_result + 1);
      }
    }
    return _result;
  }
};

struct LoopifyListPairing {
  __attribute__((pure)) static std::pair<std::shared_ptr<List<unsigned int>>,
                                         std::shared_ptr<List<unsigned int>>>
  unzip(const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> &l);
  __attribute__((pure)) static std::pair<std::shared_ptr<List<unsigned int>>,
                                         std::shared_ptr<List<unsigned int>>>
  swizzle(const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static std::pair<std::shared_ptr<List<unsigned int>>,
                                         std::shared_ptr<List<unsigned int>>>
  partition(const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
  zip_longest_fuel(const unsigned int fuel,
                   const std::shared_ptr<List<unsigned int>> &l1,
                   const std::shared_ptr<List<unsigned int>> &l2,
                   const unsigned int default0);
  static std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
  zip_longest(const std::shared_ptr<List<unsigned int>> &l1,
              const std::shared_ptr<List<unsigned int>> &l2,
              const unsigned int default0);
  static std::shared_ptr<List<unsigned int>>
  zipWith(const std::shared_ptr<List<unsigned int>> &l1,
          const std::shared_ptr<List<unsigned int>> &l2);
  __attribute__((pure)) static std::pair<std::shared_ptr<List<unsigned int>>,
                                         std::shared_ptr<List<unsigned int>>>
  split_even_odd(const std::shared_ptr<List<unsigned int>> &l);
};

#endif // INCLUDED_LOOPIFY_LIST_PAIRING
