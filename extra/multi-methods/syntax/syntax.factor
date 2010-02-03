! Copyright (C) 2008, 2010 Slava Pestov, Daniel Ehrenberg.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors arrays assocs combinators definitions effects
effects.parser help.markup help.private help.topics kernel make
multi-methods parser prettyprint prettyprint.backend
prettyprint.custom prettyprint.sections prettyprint.stylesheet
quotations see see.private sequences splitting words ;
FROM: multi-methods => methods ;
IN: multi-methods.syntax

<PRIVATE

: parse-variable-effect ( effect -- effect' variables )
    [ in>> ] 
    [ out>> { "|" } split1 ]
    [ terminated?>> swap ] tri
    [ effect boa ] [
        [
            dup array?
            [ first2 [ parse-word ] dip 2array ] when
        ] map
    ] bi* ;

: generic-stack-effect ( generic -- effect )
    [ stack-effect [ in>> ] [ out>> ] bi ]
    [ "multi-hooks" word-prop ] bi
    [ { "|" } swap 3append ] unless-empty <effect> ;

PRIVATE>

! For now: ignore uppper bounds defined in GENERIC:
! This should be fixed once the syntax is worked out
SYNTAX: MULTI-GENERIC:
    CREATE-WORD complete-effect parse-variable-effect
    [ define-generic ] [ "multi-hooks" set-word-prop ] bi-curry* bi ;

M: generic definer drop \ MULTI-GENERIC: f ;

M: generic definition drop f ;

M: generic synopsis*
    {
        [ seeing-word ]
        [ definer. ]
        [ pprint-word ]
        [ generic-stack-effect pprint-effect ]
    } cleave ;

<PRIVATE

: parse-method ( -- quot classes generic )
    parse-definition [ 2 tail ] [ second ] [ first ] tri ;

: create-method-in ( specializer generic -- method )
    create-method dup save-location f set-word ;

: effect>specializer ( effect -- specializer )
    parse-variable-effect [
        in>> [
            dup array? [
                second dup effect?
                [ drop callable ] when
            ] [ drop object ] if
        ] map
    ] dip append ;

: CREATE-METHOD ( -- method )
    scan-word complete-effect
    [ effect>specializer swap create-method-in ] keep
    dupd "multi-method-effect" set-word-prop ;

: (METHOD:) ( -- method def ) CREATE-METHOD parse-definition ;

PRIVATE>

SYNTAX: METHOD: (METHOD:) define ;

M: method-body synopsis*
    dup definer.
    [ "multi-method-generic" word-prop pprint-word ]
    [ "multi-method-effect" word-prop pprint-effect ] bi ;

M: method-body definer
    drop \ METHOD: \ ; ;

SYNTAX: METHOD\
    scan-word complete-effect effect>specializer
    swap method <wrapper> suffix! ;

<PRIVATE

! Making multimethods show up in the help of a multigeneric.
! They should also show up in the help of a class, but that'd
! require monkeypatcking or some kind of hacks with predicate
! classes that I don't want to do.

: $methods ( element -- )
    first methods values
    [ "Methods" $heading [ see-all ] ($see) ] unless-empty ;

: word-with-methods ( word -- elements )
    [
        [ (word-help) % ]
        [ \ $methods swap 2array , ] bi
    ] { } make ;

M: generic article-content word-with-methods ;

M: method-body pprint*
    \ METHOD\ pprint-word
    [ "multi-method-generic" word-prop pprint-word ]
    [ "multi-method-effect" word-prop pprint-effect ] bi ;
