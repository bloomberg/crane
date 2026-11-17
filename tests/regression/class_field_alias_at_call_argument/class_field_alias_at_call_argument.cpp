#include "class_field_alias_at_call_argument.h"



Nat ClassFieldAliasAtCallArgument::use(const std::pair<Nat, bool>& p){
return PIV<natIPtr>::ptr_to_int(p);}

