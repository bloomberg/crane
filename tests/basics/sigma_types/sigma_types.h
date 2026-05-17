#ifndef INCLUDED_SIGMA_TYPES
#define INCLUDED_SIGMA_TYPES

#include <any>
#include <memory>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a0;
    std::unique_ptr<List<A>> a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  List(const List<A> &_other) : v_(std::move(_other.clone().v_)) {}

  List(List<A> &&_other) : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  List<A> clone() const {
    List<A> _out{};

    struct _CloneFrame {
      const List<A> *_src;
      List<A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<A> *_src = _frame._src;
      List<A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->v_ =
            Cons{_alt.a0, _alt.a1 ? std::make_unique<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.a1) {
          _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a0, a1] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a0), a1 ? std::make_unique<List<A>>(*a1) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a0, List<A> a1) {
    return List(Cons{std::move(a0), std::make_unique<List<A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
        if (_alt.a1) {
          _stack.push_back(std::move(_alt.a1));
        }
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node) {
        _drain(*_node);
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename A> struct Sig {
  // TYPES
  struct Exist {
    A x;
  };

  using variant_t = std::variant<Exist>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Sig() {}

  explicit Sig(Exist _v) : v_(std::move(_v)) {}

  Sig(const Sig<A> &_other) : v_(std::move(_other.clone().v_)) {}

  Sig(Sig<A> &&_other) : v_(std::move(_other.v_)) {}

  Sig<A> &operator=(const Sig<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  Sig<A> &operator=(Sig<A> &&_other) {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  Sig<A> clone() const {
    const auto &[x] = std::get<Exist>(this->v());
    return Sig<A>(Exist{x});
  }

  // CREATORS
  template <typename _U> explicit Sig(const Sig<_U> &_other) {
    const auto &[x] = std::get<typename Sig<_U>::Exist>(_other.v());
    this->v_ = Exist{A(x)};
  }

  static Sig<A> exist(A x) { return Sig(Exist{std::move(x)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename A, typename P> struct SigT {
  // TYPES
  struct ExistT {
    A x;
    P a1;
  };

  using variant_t = std::variant<ExistT>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  SigT() {}

  explicit SigT(ExistT _v) : v_(std::move(_v)) {}

  SigT(const SigT<A, P> &_other) : v_(std::move(_other.clone().v_)) {}

  SigT(SigT<A, P> &&_other) : v_(std::move(_other.v_)) {}

  SigT<A, P> &operator=(const SigT<A, P> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  SigT<A, P> &operator=(SigT<A, P> &&_other) {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  SigT<A, P> clone() const {
    const auto &[x, a1] = std::get<ExistT>(this->v());
    return SigT<A, P>(ExistT{x, a1});
  }

  // CREATORS
  template <typename _U0, typename _U1>
  explicit SigT(const SigT<_U0, _U1> &_other) {
    const auto &[x, a1] = std::get<typename SigT<_U0, _U1>::ExistT>(_other.v());
    this->v_ = ExistT{A(x), P(a1)};
  }

  static SigT<A, P> existt(A x, P a1) {
    return SigT(ExistT{std::move(x), std::move(a1)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  A projT1() const {
    const auto &[x0, a1] = std::get<typename SigT<A, P>::ExistT>(this->v());
    return x0;
  }
};

struct SigmaTypes {
  static SigT<unsigned int, std::any> nat_with_double(unsigned int n);
  static Sig<unsigned int> positive_succ(unsigned int n);
  static unsigned int get_positive(unsigned int n);
  static Sig<unsigned int> double_positive(unsigned int n);
  static unsigned int use_nat_double(unsigned int n);
  static List<unsigned int> positives_up_to(unsigned int k);
  static inline const unsigned int test_double_5 = use_nat_double(5u);
  static inline const unsigned int test_positive_3 = get_positive(3u);
  static inline const unsigned int test_double_pos = []() {
    auto &&_sv0 = double_positive(3u);
    const auto &[x0] = std::get<typename Sig<unsigned int>::Exist>(_sv0.v());
    return x0;
  }();
  static inline const List<unsigned int> test_positives = positives_up_to(5u);
};

#endif // INCLUDED_SIGMA_TYPES
