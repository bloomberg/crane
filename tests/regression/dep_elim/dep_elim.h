#ifndef INCLUDED_DEP_ELIM
#define INCLUDED_DEP_ELIM

#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::unique_ptr<List<A>> l;
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

  List(List<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) noexcept {
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
        _dst->v_ = Cons{_alt.a, _alt.l ? std::make_unique<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.l) {
          _stack.push_back({_alt.l.get(), _dst_alt.l.get()});
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
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a), l ? std::make_unique<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_unique<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
        if (_alt.l) {
          _stack.push_back(std::move(_alt.l));
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

struct DepElim {
  struct fin {
    // TYPES
    struct FZ {
      uint64_t n;
    };

    struct FS {
      uint64_t n;
      std::unique_ptr<fin> a1;
    };

    using variant_t = std::variant<FZ, FS>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    fin() {}

    explicit fin(FZ _v) : v_(std::move(_v)) {}

    explicit fin(FS _v) : v_(std::move(_v)) {}

    fin(const fin &_other) : v_(std::move(_other.clone().v_)) {}

    fin(fin &&_other) noexcept : v_(std::move(_other.v_)) {}

    fin &operator=(const fin &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    fin &operator=(fin &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    fin clone() const {
      fin _out{};

      struct _CloneFrame {
        const fin *_src;
        fin *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const fin *_src = _frame._src;
        fin *_dst = _frame._dst;
        if (std::holds_alternative<FZ>(_src->v())) {
          const auto &_alt = std::get<FZ>(_src->v());
          _dst->v_ = FZ{_alt.n};
        } else {
          const auto &_alt = std::get<FS>(_src->v());
          _dst->v_ = FS{_alt.n, _alt.a1 ? std::make_unique<fin>() : nullptr};
          auto &_dst_alt = std::get<FS>(_dst->v_);
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static fin fz(uint64_t n) { return fin(FZ{n}); }

    static fin fs(uint64_t n, fin a1) {
      return fin(FS{n, std::make_unique<fin>(std::move(a1))});
    }

    // MANIPULATORS
    ~fin() {
      std::vector<std::unique_ptr<fin>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](fin &_node) {
        if (std::holds_alternative<FS>(_node.v_)) {
          auto &_alt = std::get<FS>(_node.v_);
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

    uint64_t fin_to_nat(uint64_t) const {
      if (std::holds_alternative<typename fin::FZ>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[n, a1] = std::get<typename fin::FS>(this->v());
        return (a1->fin_to_nat(n) + 1);
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, uint64_t &, fin &, T1 &>
    T1 fin_rec(F0 &&f, F1 &&f0, uint64_t) const {
      if (std::holds_alternative<typename fin::FZ>(this->v())) {
        const auto &[n0] = std::get<typename fin::FZ>(this->v());
        return f(n0);
      } else {
        const auto &[n0, a1] = std::get<typename fin::FS>(this->v());
        return f0(n0, *a1, a1->template fin_rec<T1>(f, f0, n0));
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, uint64_t &, fin &, T1 &>
    T1 fin_rect(F0 &&f, F1 &&f0, uint64_t) const {
      if (std::holds_alternative<typename fin::FZ>(this->v())) {
        const auto &[n0] = std::get<typename fin::FZ>(this->v());
        return f(n0);
      } else {
        const auto &[n0, a1] = std::get<typename fin::FS>(this->v());
        return f0(n0, *a1, a1->template fin_rect<T1>(f, f0, n0));
      }
    }
  };

  template <typename A> struct vec {
    // TYPES
    struct Vnil {};

    struct Vcons {
      uint64_t n;
      A a1;
      std::unique_ptr<vec<A>> a2;
    };

    using variant_t = std::variant<Vnil, Vcons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    vec() {}

    explicit vec(Vnil _v) : v_(_v) {}

    explicit vec(Vcons _v) : v_(std::move(_v)) {}

    vec(const vec<A> &_other) : v_(std::move(_other.clone().v_)) {}

    vec(vec<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

    vec<A> &operator=(const vec<A> &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    vec<A> &operator=(vec<A> &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    vec<A> clone() const {
      vec<A> _out{};

      struct _CloneFrame {
        const vec<A> *_src;
        vec<A> *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const vec<A> *_src = _frame._src;
        vec<A> *_dst = _frame._dst;
        if (std::holds_alternative<Vnil>(_src->v())) {
          _dst->v_ = Vnil{};
        } else {
          const auto &_alt = std::get<Vcons>(_src->v());
          _dst->v_ = Vcons{_alt.n, _alt.a1,
                           _alt.a2 ? std::make_unique<vec<A>>() : nullptr};
          auto &_dst_alt = std::get<Vcons>(_dst->v_);
          if (_alt.a2) {
            _stack.push_back({_alt.a2.get(), _dst_alt.a2.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    template <typename _U> explicit vec(const vec<_U> &_other) {
      if (std::holds_alternative<typename vec<_U>::Vnil>(_other.v())) {
        this->v_ = Vnil{};
      } else {
        const auto &[n, a1, a2] = std::get<typename vec<_U>::Vcons>(_other.v());
        this->v_ =
            Vcons{n, A(a1), a2 ? std::make_unique<vec<A>>(*a2) : nullptr};
      }
    }

    static vec<A> vnil() { return vec(Vnil{}); }

    static vec<A> vcons(uint64_t n, A a1, vec<A> a2) {
      return vec(
          Vcons{n, std::move(a1), std::make_unique<vec<A>>(std::move(a2))});
    }

    // MANIPULATORS
    ~vec() {
      std::vector<std::unique_ptr<vec<A>>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](vec<A> &_node) {
        if (std::holds_alternative<Vcons>(_node.v_)) {
          auto &_alt = std::get<Vcons>(_node.v_);
          if (_alt.a2) {
            _stack.push_back(std::move(_alt.a2));
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

    vec<A> vec_tail(uint64_t) const {
      if (std::holds_alternative<typename vec<A>::Vnil>(this->v())) {
        throw std::logic_error("unreachable");
      } else {
        const auto &[n, a1, a2] = std::get<typename vec<A>::Vcons>(this->v());
        return *a2;
      }
    }

    A vec_head(uint64_t) const {
      if (std::holds_alternative<typename vec<A>::Vnil>(this->v())) {
        throw std::logic_error("unreachable");
      } else {
        const auto &[n, a1, a2] = std::get<typename vec<A>::Vcons>(this->v());
        return a1;
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &>
    vec<T1> vec_map(uint64_t, F1 &&f) const {
      if (std::holds_alternative<typename vec<A>::Vnil>(this->v())) {
        return vec<T1>::vnil();
      } else {
        const auto &[n, a1, a2] = std::get<typename vec<A>::Vcons>(this->v());
        return vec<T1>::vcons(n, f(a1), a2->template vec_map<T1>(n, f));
      }
    }

    List<A> vec_to_list(uint64_t) const {
      if (std::holds_alternative<typename vec<A>::Vnil>(this->v())) {
        return List<A>::nil();
      } else {
        const auto &[n, a1, a2] = std::get<typename vec<A>::Vcons>(this->v());
        return List<A>::cons(a1, a2->vec_to_list(n));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, uint64_t &, A &, vec<A> &, T1 &>
    T1 vec_rec(T1 f, F1 &&f0, uint64_t) const {
      if (std::holds_alternative<typename vec<A>::Vnil>(this->v())) {
        return f;
      } else {
        const auto &[n0, a1, a2] = std::get<typename vec<A>::Vcons>(this->v());
        return f0(n0, a1, *a2, a2->template vec_rec<T1>(f, f0, n0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, uint64_t &, A &, vec<A> &, T1 &>
    T1 vec_rect(T1 f, F1 &&f0, uint64_t) const {
      if (std::holds_alternative<typename vec<A>::Vnil>(this->v())) {
        return f;
      } else {
        const auto &[n0, a1, a2] = std::get<typename vec<A>::Vcons>(this->v());
        return f0(n0, a1, *a2, a2->template vec_rect<T1>(f, f0, n0));
      }
    }
  };

  struct avail {
    // TYPES
    struct Present {
      uint64_t a0;
    };

    struct Absent {};

    using variant_t = std::variant<Present, Absent>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    avail() {}

    explicit avail(Present _v) : v_(std::move(_v)) {}

    explicit avail(Absent _v) : v_(_v) {}

    avail(const avail &_other) : v_(std::move(_other.clone().v_)) {}

    avail(avail &&_other) noexcept : v_(std::move(_other.v_)) {}

    avail &operator=(const avail &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    avail &operator=(avail &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    avail clone() const {
      if (std::holds_alternative<Present>(this->v())) {
        const auto &[a0] = std::get<Present>(this->v());
        return avail(Present{a0});
      } else {
        return avail(Absent{});
      }
    }

    // CREATORS
    static avail present(uint64_t a0) { return avail(Present{a0}); }

    static avail absent() { return avail(Absent{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t get_present() const {
      if (std::holds_alternative<typename avail::Present>(this->v())) {
        const auto &[a0] = std::get<typename avail::Present>(this->v());
        return a0;
      } else {
        throw std::logic_error("unreachable");
      }
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &>
    T1 avail_rec(F0 &&f, T1 f0, bool) const {
      if (std::holds_alternative<typename avail::Present>(this->v())) {
        const auto &[a0] = std::get<typename avail::Present>(this->v());
        return f(a0);
      } else {
        return f0;
      }
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &>
    T1 avail_rect(F0 &&f, T1 f0, bool) const {
      if (std::holds_alternative<typename avail::Present>(this->v())) {
        const auto &[a0] = std::get<typename avail::Present>(this->v());
        return f(a0);
      } else {
        return f0;
      }
    }
  };

  static inline const uint64_t test_fin0 =
      fin::fz(UINT64_C(2)).fin_to_nat(UINT64_C(3));
  static inline const uint64_t test_fin2 =
      fin::fs(UINT64_C(2), fin::fs(UINT64_C(1), fin::fz(UINT64_C(0))))
          .fin_to_nat(UINT64_C(3));
  static inline const vec<uint64_t> my_vec = vec<uint64_t>::vcons(
      UINT64_C(2), UINT64_C(10),
      vec<uint64_t>::vcons(UINT64_C(1), UINT64_C(20),
                           vec<uint64_t>::vcons(UINT64_C(0), UINT64_C(30),
                                                vec<uint64_t>::vnil())));
  static inline const List<uint64_t> test_vec_list =
      my_vec.vec_to_list(UINT64_C(3));
  static inline const uint64_t test_vec_head = my_vec.vec_head(UINT64_C(2));
  static inline const List<uint64_t> test_vec_tail_list =
      my_vec.vec_tail(UINT64_C(2)).vec_to_list(UINT64_C(2));
  static inline const List<uint64_t> test_vec_map =
      my_vec
          .template vec_map<uint64_t>(
              UINT64_C(3), [](uint64_t n) { return (n + UINT64_C(1)); })
          .vec_to_list(UINT64_C(3));
  static inline const uint64_t test_present =
      avail::present(UINT64_C(42)).get_present();
};

#endif // INCLUDED_DEP_ELIM
