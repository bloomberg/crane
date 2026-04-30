#ifndef INCLUDED_DEP_ELIM
#define INCLUDED_DEP_ELIM

#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  List clone() const {
    List _out{};

    struct _CloneFrame {
      const List *_src;
      List *_dst;
    };

    std::vector<_CloneFrame> _stack;
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List *_src = _frame._src;
      List *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        const auto &_alt = std::get<Nil>(_src->v());
        _dst->d_v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->d_v_ =
            Cons{_alt.d_a0, _alt.d_a1 ? std::make_unique<List>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->d_v_);
        if (_alt.d_a1)
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  static List<t_A> nil() { return List(Nil{}); }

  static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons{std::move(a0), std::make_unique<List<t_A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List>> _stack;
    auto _drain = [&](List &_node) {
      if (std::holds_alternative<Cons>(_node.d_v_)) {
        auto &_alt = std::get<Cons>(_node.d_v_);
        if (_alt.d_a1)
          _stack.push_back(std::move(_alt.d_a1));
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node)
        _drain(*_node);
    }
  }

  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }
};

struct DepElim {
  struct fin {
    // TYPES
    struct FZ {
      unsigned int d_n;
    };

    struct FS {
      unsigned int d_n;
      std::unique_ptr<fin> d_a1;
    };

    using variant_t = std::variant<FZ, FS>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    fin() {}

    explicit fin(FZ _v) : d_v_(std::move(_v)) {}

    explicit fin(FS _v) : d_v_(std::move(_v)) {}

    fin(const fin &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    fin(fin &&_other) : d_v_(std::move(_other.d_v_)) {}

    fin &operator=(const fin &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    fin &operator=(fin &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    fin clone() const {
      fin _out{};

      struct _CloneFrame {
        const fin *_src;
        fin *_dst;
      };

      std::vector<_CloneFrame> _stack;
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const fin *_src = _frame._src;
        fin *_dst = _frame._dst;
        if (std::holds_alternative<FZ>(_src->v())) {
          const auto &_alt = std::get<FZ>(_src->v());
          _dst->d_v_ = FZ{_alt.d_n};
        } else {
          const auto &_alt = std::get<FS>(_src->v());
          _dst->d_v_ =
              FS{_alt.d_n, _alt.d_a1 ? std::make_unique<fin>() : nullptr};
          auto &_dst_alt = std::get<FS>(_dst->d_v_);
          if (_alt.d_a1)
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        }
      }
      return _out;
    }

    // CREATORS
    static fin fz(unsigned int n) { return fin(FZ{std::move(n)}); }

    static fin fs(unsigned int n, fin a1) {
      return fin(FS{std::move(n), std::make_unique<fin>(std::move(a1))});
    }

    // MANIPULATORS
    ~fin() {
      std::vector<std::unique_ptr<fin>> _stack;
      auto _drain = [&](fin &_node) {
        if (std::holds_alternative<FS>(_node.d_v_)) {
          auto &_alt = std::get<FS>(_node.d_v_);
          if (_alt.d_a1)
            _stack.push_back(std::move(_alt.d_a1));
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node)
          _drain(*_node);
      }
    }

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }

    unsigned int fin_to_nat(const unsigned int &) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename fin::FZ>(_sv.v())) {
        return 0u;
      } else {
        const auto &[d_n, d_a1] = std::get<typename fin::FS>(_sv.v());
        return ((*(d_a1)).fin_to_nat(d_n) + 1);
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int, fin, T1> F1>
    T1 fin_rec(F0 &&f, F1 &&f0, const unsigned int &) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename fin::FZ>(_sv.v())) {
        const auto &[d_n] = std::get<typename fin::FZ>(_sv.v());
        return f(d_n);
      } else {
        const auto &[d_n, d_a1] = std::get<typename fin::FS>(_sv.v());
        return f0(d_n, *(d_a1), (*(d_a1)).template fin_rec<T1>(f, f0, d_n));
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int, fin, T1> F1>
    T1 fin_rect(F0 &&f, F1 &&f0, const unsigned int &) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename fin::FZ>(_sv.v())) {
        const auto &[d_n] = std::get<typename fin::FZ>(_sv.v());
        return f(d_n);
      } else {
        const auto &[d_n, d_a1] = std::get<typename fin::FS>(_sv.v());
        return f0(d_n, *(d_a1), (*(d_a1)).template fin_rect<T1>(f, f0, d_n));
      }
    }
  };

  template <typename t_A> struct vec {
    // TYPES
    struct Vnil {};

    struct Vcons {
      unsigned int d_n;
      t_A d_a1;
      std::unique_ptr<vec<t_A>> d_a2;
    };

    using variant_t = std::variant<Vnil, Vcons>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    vec() {}

    explicit vec(Vnil _v) : d_v_(_v) {}

    explicit vec(Vcons _v) : d_v_(std::move(_v)) {}

    vec(const vec<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    vec(vec<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    vec<t_A> &operator=(const vec<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    vec<t_A> &operator=(vec<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    vec clone() const {
      vec _out{};

      struct _CloneFrame {
        const vec *_src;
        vec *_dst;
      };

      std::vector<_CloneFrame> _stack;
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const vec *_src = _frame._src;
        vec *_dst = _frame._dst;
        if (std::holds_alternative<Vnil>(_src->v())) {
          const auto &_alt = std::get<Vnil>(_src->v());
          _dst->d_v_ = Vnil{};
        } else {
          const auto &_alt = std::get<Vcons>(_src->v());
          _dst->d_v_ = Vcons{_alt.d_n, _alt.d_a1,
                             _alt.d_a2 ? std::make_unique<vec>() : nullptr};
          auto &_dst_alt = std::get<Vcons>(_dst->d_v_);
          if (_alt.d_a2)
            _stack.push_back({_alt.d_a2.get(), _dst_alt.d_a2.get()});
        }
      }
      return _out;
    }

    // CREATORS
    template <typename _U> explicit vec(const vec<_U> &_other) {
      if (std::holds_alternative<typename vec<_U>::Vnil>(_other.v())) {
        d_v_ = Vnil{};
      } else {
        const auto &[d_n, d_a1, d_a2] =
            std::get<typename vec<_U>::Vcons>(_other.v());
        d_v_ = Vcons{d_n, t_A(d_a1),
                     d_a2 ? std::make_unique<vec<t_A>>(*d_a2) : nullptr};
      }
    }

    static vec<t_A> vnil() { return vec(Vnil{}); }

    static vec<t_A> vcons(unsigned int n, t_A a1, vec<t_A> a2) {
      return vec(Vcons{std::move(n), std::move(a1),
                       std::make_unique<vec<t_A>>(std::move(a2))});
    }

    // MANIPULATORS
    ~vec() {
      std::vector<std::unique_ptr<vec>> _stack;
      auto _drain = [&](vec &_node) {
        if (std::holds_alternative<Vcons>(_node.d_v_)) {
          auto &_alt = std::get<Vcons>(_node.d_v_);
          if (_alt.d_a2)
            _stack.push_back(std::move(_alt.d_a2));
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node)
          _drain(*_node);
      }
    }

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }

    vec<t_A> vec_tail(const unsigned int &) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename vec<t_A>::Vnil>(_sv.v())) {
        throw std::logic_error("unreachable");
      } else {
        const auto &[d_n, d_a1, d_a2] =
            std::get<typename vec<t_A>::Vcons>(_sv.v());
        return *(d_a2);
      }
    }

    t_A vec_head(const unsigned int &) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename vec<t_A>::Vnil>(_sv.v())) {
        throw std::logic_error("unreachable");
      } else {
        const auto &[d_n, d_a1, d_a2] =
            std::get<typename vec<t_A>::Vcons>(_sv.v());
        return d_a1;
      }
    }

    template <typename T1, MapsTo<T1, t_A> F1>
    vec<T1> vec_map(const unsigned int &, F1 &&f) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename vec<t_A>::Vnil>(_sv.v())) {
        return vec<T1>::vnil();
      } else {
        const auto &[d_n, d_a1, d_a2] =
            std::get<typename vec<t_A>::Vcons>(_sv.v());
        return vec<T1>::vcons(d_n, f(d_a1),
                              (*(d_a2)).template vec_map<T1>(d_n, f));
      }
    }

    List<t_A> vec_to_list(const unsigned int &) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename vec<t_A>::Vnil>(_sv.v())) {
        return List<t_A>::nil();
      } else {
        const auto &[d_n, d_a1, d_a2] =
            std::get<typename vec<t_A>::Vcons>(_sv.v());
        return List<t_A>::cons(d_a1, (*(d_a2)).vec_to_list(d_n));
      }
    }

    template <typename T1, MapsTo<T1, unsigned int, t_A, vec<t_A>, T1> F1>
    T1 vec_rec(const T1 f, F1 &&f0, const unsigned int &) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename vec<t_A>::Vnil>(_sv.v())) {
        return f;
      } else {
        const auto &[d_n, d_a1, d_a2] =
            std::get<typename vec<t_A>::Vcons>(_sv.v());
        return f0(d_n, d_a1, *(d_a2),
                  (*(d_a2)).template vec_rec<T1>(f, f0, d_n));
      }
    }

    template <typename T1, MapsTo<T1, unsigned int, t_A, vec<t_A>, T1> F1>
    T1 vec_rect(const T1 f, F1 &&f0, const unsigned int &) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename vec<t_A>::Vnil>(_sv.v())) {
        return f;
      } else {
        const auto &[d_n, d_a1, d_a2] =
            std::get<typename vec<t_A>::Vcons>(_sv.v());
        return f0(d_n, d_a1, *(d_a2),
                  (*(d_a2)).template vec_rect<T1>(f, f0, d_n));
      }
    }
  };

  struct avail {
    // TYPES
    struct Present {
      unsigned int d_a0;
    };

    struct Absent {};

    using variant_t = std::variant<Present, Absent>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    avail() {}

    explicit avail(Present _v) : d_v_(std::move(_v)) {}

    explicit avail(Absent _v) : d_v_(_v) {}

    avail(const avail &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    avail(avail &&_other) : d_v_(std::move(_other.d_v_)) {}

    avail &operator=(const avail &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    avail &operator=(avail &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    avail clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Present>(_sv.v())) {
        const auto &[d_a0] = std::get<Present>(_sv.v());
        return avail(Present{d_a0});
      } else {
        return avail(Absent{});
      }
    }

    // CREATORS
    static avail present(unsigned int a0) {
      return avail(Present{std::move(a0)});
    }

    static avail absent() { return avail(Absent{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }

    unsigned int get_present() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename avail::Present>(_sv.v())) {
        const auto &[d_a0] = std::get<typename avail::Present>(_sv.v());
        return d_a0;
      } else {
        throw std::logic_error("unreachable");
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0>
    T1 avail_rec(F0 &&f, const T1 f0, const bool &) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename avail::Present>(_sv.v())) {
        const auto &[d_a0] = std::get<typename avail::Present>(_sv.v());
        return f(d_a0);
      } else {
        return f0;
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0>
    T1 avail_rect(F0 &&f, const T1 f0, const bool &) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename avail::Present>(_sv.v())) {
        const auto &[d_a0] = std::get<typename avail::Present>(_sv.v());
        return f(d_a0);
      } else {
        return f0;
      }
    }
  };

  static inline const unsigned int test_fin0 = fin::fz(2u).fin_to_nat(3u);
  static inline const unsigned int test_fin2 =
      fin::fs(2u, fin::fs(1u, fin::fz(0u))).fin_to_nat(3u);
  static inline const vec<unsigned int> my_vec = vec<unsigned int>::vcons(
      2u, 10u,
      vec<unsigned int>::vcons(
          1u, 20u,
          vec<unsigned int>::vcons(0u, 30u, vec<unsigned int>::vnil())));
  static inline const List<unsigned int> test_vec_list = my_vec.vec_to_list(3u);
  static inline const unsigned int test_vec_head = my_vec.vec_head(2u);
  static inline const List<unsigned int> test_vec_tail_list =
      my_vec.vec_tail(2u).vec_to_list(2u);
  static inline const List<unsigned int> test_vec_map =
      my_vec
          .template vec_map<unsigned int>(
              3u, [](const unsigned int &n) { return (n + 1u); })
          .vec_to_list(3u);
  static inline const unsigned int test_present =
      avail::present(42u).get_present();
};

#endif // INCLUDED_DEP_ELIM
