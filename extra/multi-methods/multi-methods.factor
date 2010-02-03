! Copyright (C) 2008, 2010 Slava Pestov, Daniel Ehrenberg.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors arrays assocs classes classes.algebra
combinators compiler.units debugger definitions effects
effects.parser generalizations hashtables io kernel
kernel.private make math math.order namespaces parser
prettyprint prettyprint.backend prettyprint.custom quotations
see sequences sets shuffle sorting vectors vocabs.loader words ;
IN: multi-methods

! PART I: Converting hook specializers

: drop-n-quot ( n -- quot ) \ drop <repetition> >quotation ;

: prepare-method ( method n -- quot )
    [ 1quotation ] [ drop-n-quot ] bi* prepend ;

: prepare-methods ( methods generic -- methods' prologue )
    "multi-hooks" word-prop
    [ length [ prepare-method ] curry assoc-map ] keep
    [ [ get ] curry ] map concat [ ] like ;

! Part II: Topologically sorting specializers
: maximal-element ( seq quot -- n elt )
    dupd [
        swapd [ call +lt+ = ] 2curry filter empty?
    ] 2curry find [ "Topological sort failed" throw ] unless* ;
    inline

: topological-sort ( seq quot -- newseq )
    [ >vector [ dup empty? not ] ] dip
    [ dupd maximal-element [ over remove-nth! drop ] dip ] curry
    produce nip ; inline

: classes< ( seq1 seq2 -- lt/eq/gt )
    [
        {
            { [ 2dup eq? ] [ +eq+ ] }
            { [ 2dup [ class<= ] [ swap class<= ] 2bi and ] [ +eq+ ] }
            { [ 2dup class<= ] [ +lt+ ] }
            { [ 2dup swap class<= ] [ +gt+ ] }
            [ +eq+ ]
        } cond 2nip
    ] 2map [ +eq+ eq? not ] find nip +eq+ or ;

: sort-methods ( alist -- alist' )
    [ [ first ] bi@ classes< ] topological-sort ;

! PART III: Creating dispatch quotation
: picker ( n -- quot )
    {
        { 0 [ [ dup ] ] }
        { 1 [ [ over ] ] }
        { 2 [ [ pick ] ] }
        [ 1 - picker [ dip swap ] curry ]
    } case ;

: (multi-predicate) ( class picker -- quot )
    swap "predicate" word-prop append ;

: multi-predicate ( classes -- quot )
    dup length iota <reversed>
    [ picker 2array ] 2map
    [ drop object eq? not ] assoc-filter
    [ [ t ] ] [
        [ (multi-predicate) ] { } assoc>map
        unclip [ swap [ f ] \ if 3array append [ ] like ] reduce
    ] if-empty ;

: argument-count ( methods -- n )
    keys 0 [ length max ] reduce ;

ERROR: no-method arguments generic ;

: make-default-method ( methods generic -- quot )
    [ argument-count ] dip [ [ narray ] dip no-method ] 2curry ;

: multi-dispatch-quot ( methods generic -- quot )
    [ make-default-method ]
    [ drop [ [ multi-predicate ] dip ] assoc-map reverse ]
    2bi alist>quot ;

! Generic words
PREDICATE: generic < word
    "multi-methods" word-prop >boolean ;

: methods ( word -- alist )
    "multi-methods" word-prop >alist ;

: make-generic ( generic -- quot )
    [
        [ [ methods ] keep prepare-methods % sort-methods ] keep
        multi-dispatch-quot %
    ] [ ] make ;

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
    [ set-at ] with-methods ;

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
    generic>> methods sort-methods
    keys [ niceify-method ] map stack. ;

: forget-method ( specializer generic -- )
    [ delete-at ] with-methods ;

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
        [ H{ } clone "multi-methods" set-word-prop ]
        [ update-generic ]
        bi
    ] if ;

"multi-methods.syntax" require
