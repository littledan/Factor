USING: kernel multi-methods tools.test math arrays sequences
math.order ;
IN: multi-methods.tests

[ +lt+ ] [
    { fixnum array } { number sequence } classes<
] unit-test

[ +eq+ ] [
    { number sequence } { number sequence } classes<
] unit-test

[ +gt+ ] [
    { object object } { number sequence } classes<
] unit-test

[ V{ 1 2 10 3 4 5 } ] [ V{ 1 2 3 4 5 } clone 10 2 pick insert-nth! ] unit-test
[ V{ 1 2 10 } ] [ V{ 1 2 } clone 10 2 pick insert-nth! ] unit-test

! TODO: add in a tough testcase for multimethod sorting
