/***
  @groupdef stdlib.builtins.set Set operations

  These functions implement the basic operations on sets.
*/

/** @group stdlib.builtins.set Test if \a x is an element of the set \a y */
function     bool: 'in'(    int: x,     set of int: y) ::mzn_internal_representation;
/** @group stdlib.builtins.set \a x is an element of the set \a y */
function var bool: 'in'(var int: x, var set of int: y);
/** @group stdlib.builtins.set \a x is an element of the set \a y. False if \a x is absent. */
function var bool: 'in'(var opt int: x, set of int: y) = occurs(x) /\ deopt(x) in y;
/** @group stdlib.builtins.set Test if \a x is an element of the set \a y. False if \a x is absent. */
function     bool: 'in'(opt int: x, set of int: y) = occurs(x) /\ deopt(x) in y;
/** @group stdlib.builtins.set \a x is an element of the set \a y. False if \a x is absent. */
function var bool: 'in'(var opt int: x, var set of int: y) = occurs(x) /\ deopt(x) in y;

/** @group stdlib.builtins.set Test if \a x is an element of the set \a y */
function     bool: 'in'(    float: x,     set of float: y) ::mzn_internal_representation;
/** @group stdlib.builtins.set Test if \a x is an element of the set \a y */
function var bool: 'in'(var float: x,     set of float: y);
/** @group stdlib.builtins.set Test if \a x is an element of the set \a y. False if \a x is absent. */
function     bool: 'in'(opt float: x, set of float: y) = occurs(x) /\ deopt(x) in y;
/** @group stdlib.builtins.set \a x is an element of the set \a y. False if \a x is absent. */
function var bool: 'in'(var opt float: x, set of float: y) = occurs(x) /\ deopt(x) in y;

/** @group stdlib.builtins.set Test if \a x is a subset of \a y */
function     bool: 'subset'(    set of $T: x,      set of $T: y) ::mzn_internal_representation;
/** @group stdlib.builtins.set \a x is a subset of \a y */
function var bool: 'subset'(var set of int: x, var set of int: y);
/** @group stdlib.builtins.set Test if \a x is a superset of \a y */
function     bool: 'superset'(    set of $T: x,      set of $T: y) ::mzn_internal_representation;
/** @group stdlib.builtins.set \a x is a superset of \a y */
function var bool: 'superset'(var set of int: x, var set of int: y);

/** @group stdlib.builtins.set Return the union of sets \a x and \a y */
function     set of $T:  'union'(    set of $T: x,      set of $T: y) ::mzn_internal_representation;
/** @group stdlib.builtins.set Return the union of sets \a x and \a y */
function var set of $$T: 'union'(var set of $$T: x, var set of $$T: y) ::mzn_internal_representation;
/** @group stdlib.builtins.set Return the intersection of sets \a x and \a y */
function     set of $T:  'intersect'(    set of $T: x,      set of $T: y) ::mzn_internal_representation;
/** @group stdlib.builtins.set Return the intersection of sets \a x and \a y */
function var set of $$T: 'intersect'(var set of $$T: x, var set of $$T: y) ::mzn_internal_representation;
/** @group stdlib.builtins.set Return the set difference of sets \(\a x \setminus \a y \) */
function     set of $T:  'diff'(    set of $T: x,      set of $T: y) ::mzn_internal_representation;
/** @group stdlib.builtins.set Return the set difference of sets \(\a x \setminus \a y \) */
function var set of $$T: 'diff'(var set of $$T: x, var set of $$T: y) ::mzn_internal_representation;
/** @group stdlib.builtins.set Return the symmetric set difference of sets \a x and \a y */
function     set of $T:  'symdiff'(    set of $T: x,      set of $T: y) ::mzn_internal_representation;
/** @group stdlib.builtins.set Return the symmetric set difference of sets \a x and \a y */
function var set of $$T: 'symdiff'(var set of $$T: x, var set of $$T: y) ::mzn_internal_representation;

/** @group stdlib.builtins.set Return the set \(\{\a a,\ldots,\a b\}\) */
function set of $$E: '..'($$E: a,$$E: b) ::mzn_internal_representation;
/** @group stdlib.builtins.set Return the set \(\{\a a,\ldots,\a b\}\) */
function set of float: '..'(float: a,float: b) ::mzn_internal_representation;
/** @group stdlib.builtins.set Return the set \(\{\a a,\ldots,\a b\}\) */
function set of bool: '..'(bool: a,bool: b) =
  if a then if b then {true} else {} endif elseif b then {false,true} else {false} endif;

/** @group stdlib.builtins.set Return the set \(\{\a a,\ldots,\a b-1\}\) */
function set of $$E: '..<'($$E: a,$$E: b) = if a >= b then {} else a..enum_prev(b) endif;
/** @group stdlib.builtins.set Return the set \(\{\a a+1,\ldots,\a b\}\) */
function set of $$E: '<..'($$E: a,$$E: b) = if a >= b then {} else enum_next(a)..b endif;
/** @group stdlib.builtins.set Return the set \(\{\a a+1,\ldots,\a b-1\}\) */
function set of $$E: '<..<'($$E: a,$$E: b) = if b-a <= 1 then {} else enum_next(a)..enum_prev(b) endif;

/** @group stdlib.builtins.set Return the set \(\{\a a,\ldots,\a b-1\}\) */
function set of $$E: '..o'($$E: a) = a..max(enum_of(a));
/** @group stdlib.builtins.set Return the set \(\{\a a,\ldots,\a b-1\}\) */
function set of $$E: '..<o'($$E: a) = a..enum_prev(max(enum_of(a)));
/** @group stdlib.builtins.set Return the set \(\{\a a+1,\ldots,\a b\}\) */
function set of $$E: '<..o'($$E: a) = enum_next(a)..max(enum_of(a));
/** @group stdlib.builtins.set Return the set \(\{\a a+1,\ldots,\a b-1\}\) */
function set of $$E: '<..<o'($$E: a) = enum_next(a)..enum_prev(max(enum_of(a)));

/** @group stdlib.builtins.set Return the set \(\{\a a,\ldots,\a b-1\}\) */
function set of $$E: 'o..'($$E: a) = min(enum_of(a))..a;
/** @group stdlib.builtins.set Return the set \(\{\a a,\ldots,\a b-1\}\) */
function set of $$E: 'o..<'($$E: a) = min(enum_of(a))..enum_prev(a);
/** @group stdlib.builtins.set Return the set \(\{\a a+1,\ldots,\a b\}\) */
function set of $$E: 'o<..'($$E: a) = enum_next(min(enum_of(a)))..a;
/** @group stdlib.builtins.set Return the set \(\{\a a+1,\ldots,\a b-1\}\) */
function set of $$E: 'o<..<'($$E: a) = enum_next(min(enum_of(a)))..enum_prev(a);

function set of int: '..'() = assert(false, "internal function '..'() called", {0});
function set of $$E: '..'(set of $$E: s) = min(s)..max(s);
function set of int: '<..<'() = assert(false, "internal function '<..<'() called", {0});
function set of $$E: '<..<'(set of $$E: s) = enum_next(min(s))..enum_prev(max(s));
function set of int: '..<'() = assert(false, "internal function '..<'() called", {0});
function set of $$E: '..<'(set of $$E: s) = min(s)..enum_prev(max(s));
function set of int: '<..'() = assert(false, "internal function '<..'() called", {0});
function set of $$E: '<..'(set of $$E: s) = enum_next(min(s))..max(s);

function var set of int: '..'(var int: a, var int: b) ::promise_total =
  let {
    var set of lb(a)..ub(b): s;
    constraint forall (i in ub(s)) (i in s <-> (a <= i /\ i <= b));
  } in s;

/** @group stdlib.builtins.set Return the cardinality of the set \a x */
function     int: card(    set of $T: x);
/** @group stdlib.builtins.set Return the cardinality of the set \a x */
function var int: card(var set of int: x) ::promise_total = let {
    var 0..card(ub(x)): c;
    constraint set_card(x,c);
  } in c;

/** @group stdlib.builtins.set Return the union of the sets in array \a x */
function     set of $U:  array_union(array[$T] of     set of $U: x);
/** @group stdlib.builtins.set Return the union of the sets in array \a x */
function var set of int: array_union(array[int] of var set of int: x) ::promise_total =
    if length(x)=0 then {}
    elseif length(x)=1 then x[min(index_set(x))]
    else
      let {
        var set of ub_array(x): y;
        constraint fzn_array_set_union(x,y);
      } in y
    endif;

/** @group stdlib.builtins.set Return the intersection of the sets in array \a x */
function     set of $U:  array_intersect(array[$T] of     set of $U: x);

/** @group stdlib.builtins.set Return the intersection of the sets in array \a x. Undefined for empty \a x. */
function var set of int: array_intersect(array[int] of var set of int: x) =
    let {
      constraint length(x) > 0
    } in 
    if length(x)=0 then {}
    elseif length(x)=1 then x[min(index_set(x))]
    else
      let {
        var set of ub_array(x): y;
        constraint fzn_array_set_intersect(x,y);
      } in y
    endif;

/** @group stdlib.builtins.set Return the minimum of the set \a s */
function var $$E: min(var set of $$E: s);

/** @group stdlib.builtins.set Return the maximum of the set \a s */
function var $$E: max(var set of $$E: s);

/* Rewrite set membership on float variables to correct FlatZinc builtin */
predicate set_in(var float: x, set of float: S) = float_set_in(x, S);

/** @group stdlib.builtins.set Return a sorted list of the non-overlapping ranges in \a S */
function array[int] of int: set_to_ranges(set of int: S);
/** @group stdlib.builtins.set Return a sorted list of the non-overlapping ranges in \a S */
function array[int] of float: set_to_ranges(set of float: S);
/** @group stdlib.builtins.set Return a sorted list of the non-overlapping ranges in \a S */
function array[int] of bool: set_to_ranges(set of bool: S) =
  if S={false} then [false,false] elseif S={true} then [true,true] else [false,true] endif;

function array[int] of $$E: set_to_sparse_inverse(set of $$E: S);
