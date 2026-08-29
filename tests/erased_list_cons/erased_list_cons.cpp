#include "erased_list_cons.h"

bool MySym::t_eq_dec(MySym::Term x, MySym::Term y) {
  switch (x) {
  case Term::LBRACE: {
    switch (y) {
    case Term::LBRACE: {
      return true;
    }
    case Term::RBRACE: {
      return false;
    }
    default:
      std::unreachable();
    }
    break;
  }
  case Term::RBRACE: {
    switch (y) {
    case Term::LBRACE: {
      return false;
    }
    case Term::RBRACE: {
      return true;
    }
    default:
      std::unreachable();
    }
    break;
  }
  default:
    std::unreachable();
  }
}

bool MySym::nt_eq_dec(MySym::Nt x, MySym::Nt y) {
  switch (x) {
  case Nt::ELEM: {
    switch (y) {
    case Nt::ELEM: {
      return true;
    }
    case Nt::LST: {
      return false;
    }
    default:
      std::unreachable();
    }
    break;
  }
  case Nt::LST: {
    switch (y) {
    case Nt::ELEM: {
      return false;
    }
    case Nt::LST: {
      return true;
    }
    default:
      std::unreachable();
    }
    break;
  }
  default:
    std::unreachable();
  }
}
