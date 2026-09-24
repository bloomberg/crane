#include "class_field_alias_at_call_argument.h"



Nat ClassFieldAliasAtCallArgument::use(ptr p){return PIV<natIPtr>::ptr_to_int(std::move(p));}

