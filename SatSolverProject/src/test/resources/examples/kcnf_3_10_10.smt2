
( set-option :produce-models true )
( set-logic QF_UF )

( declare-fun p1 () Bool )
( declare-fun p2 () Bool )
( declare-fun p3 () Bool )
( declare-fun p4 () Bool )
( declare-fun p6 () Bool )
( declare-fun p7 () Bool )
( declare-fun p8 () Bool )
( declare-fun p9 () Bool )
( declare-fun p10 () Bool )
( assert ( and
( or ( not p2 ) ( not p3 ) p6 )
( or ( not p6 ) p7 ( not p8 ) )
( or ( not p8 ) p9 ( not p10 ) )
( or ( not p3 ) p4 p7 )
( or p3 p4 ( not p6 ) )
( or p2 ( not p7 ) ( not p10 ) )
( or p2 p9 p10 )
( or ( not p3 ) ( not p9 ) ( not p10 ) )
( or p2 p3 p9 )
( or ( not p1 ) p2 ( not p7 ) )
))

( check-sat )
( get-model )

