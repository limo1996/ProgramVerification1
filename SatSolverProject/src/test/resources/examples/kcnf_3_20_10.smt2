
( set-option :produce-models true )
( set-logic QF_UF )

( declare-fun p1 () Bool )
( declare-fun p2 () Bool )
( declare-fun p3 () Bool )
( declare-fun p4 () Bool )
( declare-fun p5 () Bool )
( declare-fun p7 () Bool )
( declare-fun p8 () Bool )
( declare-fun p9 () Bool )
( declare-fun p10 () Bool )
( declare-fun p11 () Bool )
( declare-fun p12 () Bool )
( declare-fun p13 () Bool )
( declare-fun p14 () Bool )
( declare-fun p15 () Bool )
( declare-fun p16 () Bool )
( declare-fun p17 () Bool )
( declare-fun p19 () Bool )
( declare-fun p20 () Bool )
( assert ( and
( or ( not p4 ) ( not p14 ) p17 )
( or p3 ( not p13 ) ( not p14 ) )
( or p7 p15 ( not p16 ) )
( or p3 ( not p7 ) p15 )
( or p3 ( not p8 ) p15 )
( or ( not p4 ) p5 p20 )
( or p10 ( not p11 ) p12 )
( or ( not p1 ) p9 p11 )
( or ( not p2 ) ( not p5 ) p14 )
( or ( not p1 ) p2 p19 )
))

( check-sat )
( get-model )

