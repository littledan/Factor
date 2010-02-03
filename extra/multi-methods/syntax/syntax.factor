! Copyright (C) 2008, 2010 Daniel Ehrenberg.
! See http://factorcode.org/license.txt for BSD license.
USING: arrays definitions effects.parser help.markup
help.private help.topics kernel make multi-methods parser
prettyprint prettyprint.backend prettyprint.custom assocs
prettyprint.sections prettyprint.stylesheet see sequences words ;
FROM: multi-methods => methods ;
IN: multi-methods.syntax

SYNTAX: MULTI-GENERIC:
    CREATE-WORD complete-effect define-generic ;

<PRIVATE

: parse-method ( -- quot classes generic )
    parse-definition [ 2 tail ] [ second ] [ first ] tri ;

: create-method-in ( specializer generic -- method )
    create-method dup save-location f set-word ;

: CREATE-METHOD ( -- method )
    scan-word scan-object swap create-method-in ;

: (METHOD:) ( -- method def ) CREATE-METHOD parse-definition ;

PRIVATE>

SYNTAX: METHOD: (METHOD:) define ;

M: generic definer drop \ MULTI-GENERIC: f ;

M: generic definition drop f ;

M: method-body synopsis*
    dup definer.
    [ "multi-method-generic" word-prop pprint-word ]
    [ "multi-method-specializer" word-prop pprint* ] bi ;

M: method-body definer
    drop \ METHOD: \ ; ;

SYNTAX: METHOD\ scan-word scan-object swap method <wrapper> suffix! ;

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
    [
        [
            [ "METHOD\\ " % "multi-method-generic" word-prop word-name* % ]
            [ " " % "multi-method-specializer" word-prop unparse % ]
            bi
        ] "" make
    ] [ word-style ] bi styled-text ;
