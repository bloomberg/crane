#include "st_arrays.h"

uint64_t StArrays::array_simp_fixed_init() {
  std::vector<uint64_t> * arr;
  arr = new std::remove_pointer_t<decltype(arr)>(nat_idx::suc(
      nat_idx::suc(nat_idx::suc(nat_idx::suc(nat_idx::suc(nat_idx::zero()))))) -
                                                 nat_idx::zero() + 1,
                                                 UINT64_C(5));
  return (*std::move(arr))[nat_idx::suc(nat_idx::zero())];
}

std::pair<std::pair<uint64_t, uint64_t>, List<uint64_t>>
StArrays::array_simp_list() {
  std::vector<uint64_t> * arr;
  arr = new std::remove_pointer_t<decltype(arr)>(
      nat_idx::suc(nat_idx::suc(nat_idx::suc(nat_idx::zero()))) -
      nat_idx::zero() + 1);
  {
    auto _xs = List<uint64_t>::cons(
        UINT64_C(5),
        List<uint64_t>::cons(
            UINT64_C(4),
            List<uint64_t>::cons(
                UINT64_C(3),
                List<uint64_t>::cons(UINT64_C(2), List<uint64_t>::nil()))));
    for (size_t _i = 0; _i < arr->size(); _i++) {
      if (holds_alternative<typename std::remove_cvref_t<decltype(_xs)>::Cons>(
              _xs.v())) {
        const auto &[_a, _l] =
            get<typename std::remove_cvref_t<decltype(_xs)>::Cons>(_xs.v());
        (*arr)[_i] = _a;
        if (_l) _xs = *_l;
      }
    }
  };
  uint64_t elem = (*arr)[nat_idx::zero()];
  auto &&_once1 = std::move(arr);
  List<uint64_t> lst = [&]() {
    using _E = typename std::remove_pointer_t<
        std::remove_cvref_t<decltype(_once1)>>::value_type;
    List<_E> _r = List<_E>::nil();
    for (size_t _i = _once1->size(); _i > 0; _i--) {
      _r = List<_E>::cons((*_once1)[_i - 1], std::move(_r));
    }
    return _r;
  }();
  return std::make_pair(std::make_pair(elem, lst.length()), lst);
}

List<uint64_t> StArrays::swap_first_and_last_list(const List<uint64_t> &xs) {
  std::vector<uint64_t> * arr;
  arr = new std::remove_pointer_t<decltype(arr)>(
      nat_idx::fromNat((((xs.length() - UINT64_C(1)) > xs.length()
                             ? 0
                             : (xs.length() - UINT64_C(1))))) -
      nat_idx::zero() + 1);
  {
    auto _xs = xs;
    for (size_t _i = 0; _i < arr->size(); _i++) {
      if (holds_alternative<typename std::remove_cvref_t<decltype(_xs)>::Cons>(
              _xs.v())) {
        const auto &[_a, _l] =
            get<typename std::remove_cvref_t<decltype(_xs)>::Cons>(_xs.v());
        (*arr)[_i] = _a;
        if (_l) _xs = *_l;
      }
    }
  };
  [&]() {
    uint64_t vi = (*arr)[nat_idx::zero()];
    auto _once1 = xs.length();
    uint64_t vj =
        (*arr)[nat_idx::fromNat(
             (((_once1 - UINT64_C(1)) > _once1 ? 0 : (_once1 - UINT64_C(1)))))];
    (*arr)[nat_idx::zero()] = vj;
    auto _once2 = xs.length();
    (*arr)[nat_idx::fromNat(
         (((_once2 - UINT64_C(1)) > _once2 ? 0 : (_once2 - UINT64_C(1)))))] =
        vi;
    return std::monostate{};
  }();
  auto &&_once3 = std::move(arr);
  return [&]() {
    using _E = typename std::remove_pointer_t<
        std::remove_cvref_t<decltype(_once3)>>::value_type;
    List<_E> _r = List<_E>::nil();
    for (size_t _i = _once3->size(); _i > 0; _i--) {
      _r = List<_E>::cons((*_once3)[_i - 1], std::move(_r));
    }
    return _r;
  }();
}

uint64_t StArrays::nth(uint64_t n, const List<uint64_t> &l, uint64_t default0) {
  if (n <= 0) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a0, _] = std::get<typename List<uint64_t>::Cons>(l.v());
      return a0;
    }
  } else {
    uint64_t m = n - 1;
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[_, a10] = std::get<typename List<uint64_t>::Cons>(l.v());
      return nth(m, *a10, default0);
    }
  }
}

List<uint64_t> ListDef::seq(uint64_t start, uint64_t len) {
  if (len <= 0) {
    return List<uint64_t>::nil();
  } else {
    uint64_t len0 = len - 1;
    return List<uint64_t>::cons(start, ListDef::seq((start + 1), len0));
  }
}
