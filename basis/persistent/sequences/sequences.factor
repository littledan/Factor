! Copyright (C) 2008 Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: sequences kernel ;
IN: persistent.sequences

GENERIC: ppush ( val seq -- seq' )

M: sequence ppush swap suffix ;

GENERIC: ppop ( seq -- seq' )

M: sequence ppop 1 head* ;

GENERIC: new-nth ( val i seq -- seq' )

M: sequence new-nth clone [ set-nth ] keep ;