( set-option :produce-models true )
( set-logic QF_UF )

( declare-fun p1 () Bool )
( declare-fun p2 () Bool )
( declare-fun p3 () Bool )

( assert ( and 
 ( or p1 ( not p3 )  )
 ( or p2 p3 ( not p1 )  )
))

( check-sat )
( get-model )