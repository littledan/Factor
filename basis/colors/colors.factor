! Copyright (C) 2003, 2009 Slava Pestov.
! Copyright (C) 2008 Eduardo Cavazos.
! See http://factorcode.org/license.txt for BSD license.
USING: kernel accessors combinators math ;
IN: colors

TUPLE: color ;

TUPLE: rgba < color
{ red read-only }
{ green read-only }
{ blue read-only }
{ alpha read-only } ;

C: <rgba> rgba

GENERIC: >rgba ( color -- rgba )

M: rgba >rgba ( rgba -- rgba ) ;

M: color red>> ( color -- red ) >rgba red>> ;
M: color green>> ( color -- green ) >rgba green>> ;
M: color blue>> ( color -- blue ) >rgba blue>> ;

: >rgba-components ( object -- r g b a )
    >rgba { [ red>> ] [ green>> ] [ blue>> ] [ alpha>> ] } cleave ; inline

: opaque? ( color -- ? ) alpha>> 1 number= ;

CONSTANT: transparent T{ rgba f 0.0 0.0 0.0 0.0 }