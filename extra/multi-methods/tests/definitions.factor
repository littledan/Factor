USING: multi-methods tools.test math sequences namespaces system
kernel strings words compiler.units quotations ;
IN: multi-methods.tests

DEFER: fake
\ fake H{ } clone "multi-methods" set-word-prop
\ fake V{ } clone "method-list" set-word-prop
<< (( -- )) \ fake set-stack-effect >>

[
    [ "fake-{ }" ] [ { } \ fake method-word-name ] unit-test

    [ H{ { "multi-method-generic" fake } { "multi-method-specializer" { } } } ]
    [ { } \ fake method-word-props ] unit-test

    [ t ] [ { } \ fake <method> method-body? ] unit-test

    [ V{ } [ ] ] [ \ fake [ methods ] keep prepare-methods ] unit-test

    [ t ] [ \ fake make-generic callable? ] unit-test

    [ ] [ \ fake update-generic ] unit-test

    DEFER: testing

    [ ] [ \ testing (( -- )) { } define-generic ] unit-test

    [ t ] [ \ testing generic? ] unit-test
] with-compilation-unit

[ 5 "hi" t ] [ 5 "hi" { integer string } prepare-specifier 2 [works?] call ] unit-test
[ "hi" 5 f ] [ "hi" 5 { integer string } prepare-specifier 2 [works?] call ] unit-test
[ "hi" "hi" f ] [ "hi" "hi" { integer string } prepare-specifier 2 [works?] call ] unit-test
[ 5 5 f ] [ 5 5 { integer string } prepare-specifier 2 [works?] call ] unit-test
