! Copyright (C) 2008, 2010 Slava Pestov, Daniel Ehrenberg.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors arrays assocs classes classes.algebra
combinators compiler.units debugger definitions effects
effects.parser generalizations hashtables io kernel fry
kernel.private make math math.order namespaces parser
prettyprint prettyprint.backend prettyprint.custom quotations
see sequences sets shuffle sorting vectors vocabs.loader words
macros combinators.short-circuit locals ;
IN: multi-methods

! Dropping hook variables before method calls
: prepare-method ( method n -- quot )
    swap '[ _ ndrop _ execute ] ;

: prepare-methods ( methods generic -- methods' prologue )
    "multi-hooks" word-prop
    [ length [ prepare-method ] curry assoc-map ] keep
    [ [ get ] curry ] map concat [ ] like ;

! Topologically sorting specializers, online as they are added
: classes< ( seq1 seq2 -- lt/eq/gt )
    [
        {
            { [ 2dup eq? ] [ +eq+ ] }
            { [ 2dup [ class<= ] [ swap class<= ] 2bi and ] [ +eq+ ] }
            { [ 2dup class<= ] [ +lt+ ] }
            { [ 2dup swap class<= ] [ +gt+ ] }
            [ +eq+ ]
        } cond 2nip
    ] 2map [ +eq+ = not ] find nip +eq+ or ;

: insert-nth! ( elt i seq -- )
    {
        [ swap tail ]
        [ set-length ]
        [ nip swapd push ]
        [ nip push-all ]
    } 2cleave ;

: find-position ( spec/method method-list -- i )
    [ [ first ] bi@ class< +gt+ = ] with find-last drop
    0 or ;

: insert-method ( spec/method method-list -- )
    2dup find-position swap insert-nth! ;

! PART III: Creating dispatch quotation
ERROR: no-method arguments generic ;

: make-default-method ( generic -- quot )
    [ stack-effect in>> length ] keep
    [ "multi-hooks" word-prop ] keep
    [ [ narray ] [ [ get ] map append ] [ ] tri* no-method ] 3curry ;

! Generic words
PREDICATE: generic < word
    "multi-methods" word-prop >boolean ;

: methods ( word -- alist )
    "method-list" word-prop ;

: [works?] ( len -- quot )
    iota [
        [ 1 + ] keep '[
            [ _ npick ] dip
            _ swap nth
            call( object -- ? )
        ]
    ] map '[ _ 1&& ] ;

: prepare-specifier ( specifier -- specifier' )
    reverse [ "predicate" word-prop ] map ;

MACRO:: dispatch ( hooks effect default -- quot )
    effect in>> length :> #args
    #args hooks length + [works?] :> checker
    [
        hooks [ '[ _ get ] ] map concat '[ _ dip ] %
        [ [ third checker call ] find-last nip ] %
        hooks length '[ _ nnip ] %
        [
            [ second effect execute-effect ]
            [ default effect call-effect ] if*
        ] %
    ] [ ] make ;

: make-generic ( generic -- quot )
    {
        [ methods ]
        [ "multi-hooks" word-prop ]
        [ stack-effect ]
        [ make-default-method ]
    } cleave
    '[ _ _ _ _ dispatch ] ;

: update-generic ( word -- )
    dup make-generic define ;

! Methods
PREDICATE: method-body < word
    "multi-method-generic" word-prop >boolean ;

M: method-body stack-effect
    "multi-method-generic" word-prop stack-effect ;

M: method-body crossref?
    "forgotten" word-prop not ;

: method-word-name ( specializer generic -- string )
    [ name>> % "-" % unparse % ] "" make ;

: method-word-props ( specializer generic -- assoc )
    [
        "multi-method-generic" set
        "multi-method-specializer" set
    ] H{ } make-assoc ;

ERROR: extra-hooks ;

: check-hooks ( specializer generic -- )
    [ [ array? ] filter [ first ] map ]
    [ "multi-hooks" word-prop ] bi*
    subset? [ extra-hooks ] unless ;

: <method> ( specializer generic -- word )
    2dup check-hooks
    [ method-word-props ] 2keep
    method-word-name f <word>
    swap >>props ;

: with-methods ( word quot -- )
    over [
        [ "multi-methods" word-prop ] dip call
    ] dip update-generic ; inline

: reveal-method ( method classes generic -- )
    [
        [ swap over prepare-specifier 3array ]
        [ "method-list" word-prop ] bi* insert-method
    ] [ [ set-at ] with-methods ] 3bi ;

: method ( classes word -- method )
    "multi-methods" word-prop at ;

: create-method ( classes generic -- method )
    2dup method dup [
        2nip
    ] [
        drop [ <method> dup ] 2keep reveal-method
    ] if ;

: niceify-method ( seq -- seq )
    [ dup \ f eq? [ drop f ] when ] map ;

M: no-method error.
    "Type check error" print
    nl
    "Generic word " write dup generic>> pprint
    " does not have a method applicable to inputs:" print
    dup arguments>> short.
    nl
    "Inputs have signature:" print
    dup arguments>> [ class ] map niceify-method .
    nl
    "Available methods: " print
    generic>> methods
    keys [ niceify-method ] map stack. ;

: forget-method ( specializer generic -- )
    [ "method-list" word-prop swap '[ first _ = not ] filter! drop ]
    [ [ delete-at ] with-methods ] 2bi ;

M: method-body forget*
    [
        "multi-method-specializer" "multi-method-generic"
        [ word-prop ] bi-curry@ bi forget-method
    ] [ call-next-method ] bi ;

M: generic forget*
    [ methods values [ forget ] each ] [ call-next-method ] bi ;

: define-generic ( word effect -- )
    over set-stack-effect
    dup "multi-methods" word-prop [ drop ] [
        [ V{ } clone "method-list" set-word-prop ]
        [ H{ } clone "multi-methods" set-word-prop ]
        [ update-generic ]
        tri
    ] if ;

"multi-methods.syntax" require
