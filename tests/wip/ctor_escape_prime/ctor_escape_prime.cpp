#include <algorithm>
#include <any>
#include <cassert>
#include <ctor_escape_prime.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int CtorEscapePrime::tag(const CtorEscapePrime::item x){return
                                                                 [&](void) {
                                                                   switch (x) {
 case item::T': {
 return (0 + 1);
 }
 case item::T_: {
   return ((0 + 1) + 1);
 }
 }
                                                                 }();
}
