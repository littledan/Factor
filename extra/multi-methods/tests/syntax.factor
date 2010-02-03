USING: multi-methods multi-methods.syntax tools.test math
sequences namespaces system eval
kernel strings definitions prettyprint debugger arrays
hashtables continuations classes assocs accessors see ;
IN: multi-methods.tests

MULTI-GENERIC: first-test ( -- )

[ t ] [ \ first-test generic? ] unit-test

MIXIN: thing

SINGLETON: paper    INSTANCE: paper thing
SINGLETON: scissors INSTANCE: scissors thing
SINGLETON: rock     INSTANCE: rock thing

MULTI-GENERIC: beats? ( obj1 obj2 -- ? )

METHOD: beats? ( paper scissors -- ? ) 2drop t ;
METHOD: beats? ( scissors obj2: rock -- ? ) 2drop t ;
METHOD: beats? ( obj1: rock paper -- ? ) 2drop t ;
METHOD: beats? ( obj1: thing obj2: thing -- ? ) 2drop f ;

: play ( obj1 obj2 -- ? ) beats? ;

[ { } 3 play ] must-fail
[ t ] [ error get no-method? ] unit-test
[ ] [ error get error. ] unit-test
[ { { } 3 } ] [ error get arguments>> ] unit-test
[ t ] [ paper scissors play ] unit-test
[ f ] [ scissors paper play ] unit-test

[ ] [ METHOD\ beats? ( obj1: paper obj2: scissors -- ? ) see ] unit-test

SYMBOL: some-var

MULTI-GENERIC: hook-test ( obj -- obj | some-var )

METHOD: hook-test ( foo: array -- bar | some-var: array ) reverse ;
METHOD: hook-test ( object -- obj | some-var: array ) class ;
METHOD: hook-test ( foo: hashtable -- obj | some-var: number ) assoc-size ;

{ 1 2 3 } some-var set
[ { f t t } ] [ { t t f } hook-test ] unit-test
[ fixnum ] [ 3 hook-test ] unit-test
5.0 some-var set
[ 0 ] [ H{ } hook-test ] unit-test

"error" some-var set
[ H{ } hook-test ] must-fail
[ t ] [ error get no-method? ] unit-test
[ { H{ } "error" } ] [ error get arguments>> ] unit-test

MIXIN: busted

TUPLE: busted-1 ;
TUPLE: busted-2 ; INSTANCE: busted-2 busted
TUPLE: busted-3 ;

MULTI-GENERIC: busted-sort ( obj1 obj2 -- obj1 obj2 )

METHOD: busted-sort ( obj: busted-1 obj: busted-2 -- obj obj ) ;
METHOD: busted-sort ( obj: busted-2 obj: busted-3 -- obj obj ) ;
METHOD: busted-sort ( obj: busted obj: busted -- obj obj ) ;

[ "USING: multi-methods.syntax multi-methods.tests arrays ;
METHOD: busted-sort ( a b -- c d | some-var: array ) ;" eval( -- ) ] must-fail
