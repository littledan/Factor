! Copyright (C) 2008, 2010 Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: kernel math math.order sequences accessors arrays
byte-arrays layouts classes.tuple.private fry locals
compiler.tree.propagation.info compiler.cfg.hats
compiler.cfg.instructions compiler.cfg.stacks
compiler.cfg.utilities compiler.cfg.builder.blocks ;
IN: compiler.cfg.intrinsics.allot

: ##set-slots ( regs obj class -- )
    '[ _ swap 1 + _ type-number ##set-slot-imm ] each-index ;

: emit-simple-allot ( node -- )
    [ in-d>> length ] [ node-output-infos first class>> ] bi
    [ drop ds-load ] [ [ 1 + cells ] dip ^^allot ] [ nip ] 2tri
    [ ##set-slots ] [ [ drop ] [ ds-push ] [ drop ] tri* ] 3bi ;

: tuple-slot-regs ( layout -- vregs )
    [ second ds-load ] [ ^^load-literal ] bi prefix ;

: ^^allot-tuple ( n -- dst )
    2 + cells tuple ^^allot ;

: emit-<tuple-boa> ( node -- )
    dup node-input-infos last literal>>
    dup array? [
        nip
        ds-drop
        [ tuple-slot-regs ] [ second ^^allot-tuple ] bi
        [ tuple ##set-slots ] [ ds-push drop ] 2bi
    ] [ drop emit-primitive ] if ;

: store-length ( len reg class -- )
    [ [ ^^load-literal ] dip 1 ] dip type-number ##set-slot-imm ;

:: store-initial-element ( len reg elt class -- )
    len [ [ elt reg ] dip 2 + class type-number ##set-slot-imm ] each-integer ;

: expand-<array>? ( obj -- ? )
    dup integer? [ 0 8 between? ] [ drop f ] if ;

: ^^allot-array ( n -- dst )
    2 + cells array ^^allot ;

:: emit-<array> ( node -- )
    node node-input-infos first literal>> :> len
    len expand-<array>? [
        ds-pop :> elt
        len ^^allot-array :> reg
        ds-drop
        len reg array store-length
        len reg elt array store-initial-element
        reg ds-push
    ] [ node emit-primitive ] if ;

: expand-(byte-array)? ( obj -- ? )
    dup integer? [ 0 1024 between? ] [ drop f ] if ;

: expand-<byte-array>? ( obj -- ? )
    dup integer? [ 0 32 between? ] [ drop f ] if ;

: bytes>cells ( m -- n ) cell align cell /i ;

: ^^allot-byte-array ( n -- dst )
    16 + byte-array ^^allot ;

: emit-allot-byte-array ( len -- dst )
    ds-drop
    dup ^^allot-byte-array
    [ byte-array store-length ] [ ds-push ] [ ] tri ;

: emit-(byte-array) ( node -- )
    dup node-input-infos first literal>> dup expand-(byte-array)?
    [ nip emit-allot-byte-array drop ] [ drop emit-primitive ] if ;

:: emit-<byte-array> ( node -- )
    node node-input-infos first literal>> dup expand-<byte-array>? [
        :> len
        0 ^^load-literal :> elt
        len emit-allot-byte-array :> reg
        len reg elt byte-array store-initial-element
    ] [ drop node emit-primitive ] if ;
