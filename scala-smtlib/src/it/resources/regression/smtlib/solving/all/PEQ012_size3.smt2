(set-option :print-success true)
(set-logic QF_UF)
(set-info :source |
CADE ATP System competition. See http://www.cs.miami.edu/~tptp/CASC
 for more information. 

This benchmark was obtained by trying to find a finite model of a first-order 
formula (Albert Oliveras).
|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)
(declare-sort U 0)
(declare-fun f1 (U U) U)
(declare-fun c6 () U)
(declare-fun c3 () U)
(declare-fun c7 () U)
(declare-fun c5 () U)
(declare-fun c2 () U)
(declare-fun c4 () U)
(declare-fun c8 () U)
(declare-fun c9 () U)
(declare-fun c_0 () U)
(declare-fun c_1 () U)
(declare-fun c_2 () U)
(assert (let ((?v_0 (f1 c_0 c_0)) (?v_2 (= c_0 c_0))) (let ((?v_18 (or (not (= ?v_0 ?v_0)) ?v_2)) (?v_6 (f1 c_1 c_0)) (?v_3 (= c_0 c_1)) (?v_7 (f1 c_2 c_0)) (?v_4 (= c_0 c_2)) (?v_1 (f1 c_0 c_1))) (let ((?v_19 (not (= ?v_1 ?v_1))) (?v_8 (f1 c_1 c_1)) (?v_11 (f1 c_2 c_1)) (?v_5 (f1 c_0 c_2))) (let ((?v_20 (not (= ?v_5 ?v_5))) (?v_13 (f1 c_1 c_2)) (?v_14 (f1 c_2 c_2)) (?v_9 (= c_1 c_0)) (?v_21 (not (= ?v_6 ?v_6))) (?v_10 (= c_1 c_1)) (?v_12 (= c_1 c_2))) (let ((?v_22 (or (not (= ?v_8 ?v_8)) ?v_10)) (?v_23 (not (= ?v_13 ?v_13))) (?v_15 (= c_2 c_0)) (?v_16 (= c_2 c_1)) (?v_24 (not (= ?v_7 ?v_7))) (?v_17 (= c_2 c_2)) (?v_25 (not (= ?v_11 ?v_11)))) (let ((?v_26 (or (not (= ?v_14 ?v_14)) ?v_17)) (?v_27 (f1 c_0 ?v_0)) (?v_34 (f1 c_0 ?v_1)) (?v_40 (f1 c_0 ?v_5)) (?v_33 (f1 c_0 ?v_6)) (?v_51 (f1 c_0 ?v_8)) (?v_58 (f1 c_0 ?v_13)) (?v_39 (f1 c_0 ?v_7)) (?v_57 (f1 c_0 ?v_11)) (?v_75 (f1 c_0 ?v_14)) (?v_29 (f1 c_1 ?v_0)) (?v_36 (f1 c_1 ?v_1)) (?v_42 (f1 c_1 ?v_5)) (?v_35 (f1 c_1 ?v_6)) (?v_53 (f1 c_1 ?v_8)) (?v_60 (f1 c_1 ?v_13)) (?v_41 (f1 c_1 ?v_7)) (?v_59 (f1 c_1 ?v_11)) (?v_77 (f1 c_1 ?v_14)) (?v_31 (f1 c_2 ?v_0)) (?v_38 (f1 c_2 ?v_1)) (?v_44 (f1 c_2 ?v_5)) (?v_37 (f1 c_2 ?v_6)) (?v_55 (f1 c_2 ?v_8)) (?v_62 (f1 c_2 ?v_13)) (?v_43 (f1 c_2 ?v_7)) (?v_61 (f1 c_2 ?v_11)) (?v_79 (f1 c_2 ?v_14))) (let ((?v_28 (f1 c_0 (f1 c_0 ?v_27))) (?v_30 (f1 c_0 (f1 c_0 ?v_29))) (?v_32 (f1 c_0 (f1 c_0 ?v_31))) (?v_46 (f1 c_0 (f1 c_1 ?v_33))) (?v_45 (f1 c_1 (f1 c_0 ?v_34))) (?v_48 (f1 c_0 (f1 c_1 ?v_35))) (?v_47 (f1 c_1 (f1 c_0 ?v_36))) (?v_50 (f1 c_0 (f1 c_1 ?v_37))) (?v_49 (f1 c_1 (f1 c_0 ?v_38))) (?v_64 (f1 c_0 (f1 c_2 ?v_39))) (?v_63 (f1 c_2 (f1 c_0 ?v_40))) (?v_66 (f1 c_0 (f1 c_2 ?v_41))) (?v_65 (f1 c_2 (f1 c_0 ?v_42))) (?v_68 (f1 c_0 (f1 c_2 ?v_43))) (?v_67 (f1 c_2 (f1 c_0 ?v_44))) (?v_52 (f1 c_1 (f1 c_1 ?v_51))) (?v_54 (f1 c_1 (f1 c_1 ?v_53))) (?v_56 (f1 c_1 (f1 c_1 ?v_55))) (?v_70 (f1 c_1 (f1 c_2 ?v_57))) (?v_69 (f1 c_2 (f1 c_1 ?v_58))) (?v_72 (f1 c_1 (f1 c_2 ?v_59))) (?v_71 (f1 c_2 (f1 c_1 ?v_60))) (?v_74 (f1 c_1 (f1 c_2 ?v_61))) (?v_73 (f1 c_2 (f1 c_1 ?v_62))) (?v_76 (f1 c_2 (f1 c_2 ?v_75))) (?v_78 (f1 c_2 (f1 c_2 ?v_77))) (?v_80 (f1 c_2 (f1 c_2 ?v_79)))) (and (distinct c_0 c_1 c_2) ?v_18 (or (not (= ?v_0 ?v_6)) ?v_3) (or (not (= ?v_0 ?v_7)) ?v_4) (or ?v_19 ?v_2) (or (not (= ?v_1 ?v_8)) ?v_3) (or (not (= ?v_1 ?v_11)) ?v_4) (or ?v_20 ?v_2) (or (not (= ?v_5 ?v_13)) ?v_3) (or (not (= ?v_5 ?v_14)) ?v_4) (or (not (= ?v_6 ?v_0)) ?v_9) (or ?v_21 ?v_10) (or (not (= ?v_6 ?v_7)) ?v_12) (or (not (= ?v_8 ?v_1)) ?v_9) ?v_22 (or (not (= ?v_8 ?v_11)) ?v_12) (or (not (= ?v_13 ?v_5)) ?v_9) (or ?v_23 ?v_10) (or (not (= ?v_13 ?v_14)) ?v_12) (or (not (= ?v_7 ?v_0)) ?v_15) (or (not (= ?v_7 ?v_6)) ?v_16) (or ?v_24 ?v_17) (or (not (= ?v_11 ?v_1)) ?v_15) (or (not (= ?v_11 ?v_8)) ?v_16) (or ?v_25 ?v_17) (or (not (= ?v_14 ?v_5)) ?v_15) (or (not (= ?v_14 ?v_13)) ?v_16) ?v_26 ?v_18 (or (not (= ?v_0 ?v_1)) ?v_3) (or (not (= ?v_0 ?v_5)) ?v_4) (or (not (= ?v_1 ?v_0)) ?v_9) (or ?v_19 ?v_10) (or (not (= ?v_1 ?v_5)) ?v_12) (or (not (= ?v_5 ?v_0)) ?v_15) (or (not (= ?v_5 ?v_1)) ?v_16) (or ?v_20 ?v_17) (or ?v_21 ?v_2) (or (not (= ?v_6 ?v_8)) ?v_3) (or (not (= ?v_6 ?v_13)) ?v_4) (or (not (= ?v_8 ?v_6)) ?v_9) ?v_22 (or (not (= ?v_8 ?v_13)) ?v_12) (or (not (= ?v_13 ?v_6)) ?v_15) (or (not (= ?v_13 ?v_8)) ?v_16) (or ?v_23 ?v_17) (or ?v_24 ?v_2) (or (not (= ?v_7 ?v_11)) ?v_3) (or (not (= ?v_7 ?v_14)) ?v_4) (or (not (= ?v_11 ?v_7)) ?v_9) (or ?v_25 ?v_10) (or (not (= ?v_11 ?v_14)) ?v_12) (or (not (= ?v_14 ?v_7)) ?v_15) (or (not (= ?v_14 ?v_11)) ?v_16) ?v_26 (= (f1 ?v_0 c_0) ?v_27) (= (f1 ?v_0 c_1) ?v_34) (= (f1 ?v_0 c_2) ?v_40) (= (f1 ?v_1 c_0) ?v_33) (= (f1 ?v_1 c_1) ?v_51) (= (f1 ?v_1 c_2) ?v_58) (= (f1 ?v_5 c_0) ?v_39) (= (f1 ?v_5 c_1) ?v_57) (= (f1 ?v_5 c_2) ?v_75) (= (f1 ?v_6 c_0) ?v_29) (= (f1 ?v_6 c_1) ?v_36) (= (f1 ?v_6 c_2) ?v_42) (= (f1 ?v_8 c_0) ?v_35) (= (f1 ?v_8 c_1) ?v_53) (= (f1 ?v_8 c_2) ?v_60) (= (f1 ?v_13 c_0) ?v_41) (= (f1 ?v_13 c_1) ?v_59) (= (f1 ?v_13 c_2) ?v_77) (= (f1 ?v_7 c_0) ?v_31) (= (f1 ?v_7 c_1) ?v_38) (= (f1 ?v_7 c_2) ?v_44) (= (f1 ?v_11 c_0) ?v_37) (= (f1 ?v_11 c_1) ?v_55) (= (f1 ?v_11 c_2) ?v_62) (= (f1 ?v_14 c_0) ?v_43) (= (f1 ?v_14 c_1) ?v_61) (= (f1 ?v_14 c_2) ?v_79) (= ?v_28 ?v_28) (= ?v_30 ?v_30) (= ?v_32 ?v_32) (= ?v_46 ?v_45) (= ?v_48 ?v_47) (= ?v_50 ?v_49) (= ?v_64 ?v_63) (= ?v_66 ?v_65) (= ?v_68 ?v_67) (= ?v_45 ?v_46) (= ?v_47 ?v_48) (= ?v_49 ?v_50) (= ?v_52 ?v_52) (= ?v_54 ?v_54) (= ?v_56 ?v_56) (= ?v_70 ?v_69) (= ?v_72 ?v_71) (= ?v_74 ?v_73) (= ?v_63 ?v_64) (= ?v_65 ?v_66) (= ?v_67 ?v_68) (= ?v_69 ?v_70) (= ?v_71 ?v_72) (= ?v_73 ?v_74) (= ?v_76 ?v_76) (= ?v_78 ?v_78) (= ?v_80 ?v_80) (= (f1 c6 c3) (f1 c7 c5)) (= (f1 c2 c3) (f1 c4 c5)) (= (f1 c2 c8) (f1 c4 c9)) (not (= (f1 c6 c8) (f1 c7 c9))) (or (= ?v_0 c_0) (= ?v_0 c_1) (= ?v_0 c_2)) (or (= ?v_1 c_0) (= ?v_1 c_1) (= ?v_1 c_2)) (or (= ?v_5 c_0) (= ?v_5 c_1) (= ?v_5 c_2)) (or (= ?v_6 c_0) (= ?v_6 c_1) (= ?v_6 c_2)) (or (= ?v_8 c_0) (= ?v_8 c_1) (= ?v_8 c_2)) (or (= ?v_13 c_0) (= ?v_13 c_1) (= ?v_13 c_2)) (or (= ?v_7 c_0) (= ?v_7 c_1) (= ?v_7 c_2)) (or (= ?v_11 c_0) (= ?v_11 c_1) (= ?v_11 c_2)) (or (= ?v_14 c_0) (= ?v_14 c_1) (= ?v_14 c_2)) (or (= c6 c_0) (= c6 c_1) (= c6 c_2)) (or (= c3 c_0) (= c3 c_1) (= c3 c_2)) (or (= c7 c_0) (= c7 c_1) (= c7 c_2)) (or (= c5 c_0) (= c5 c_1) (= c5 c_2)) (or (= c2 c_0) (= c2 c_1) (= c2 c_2)) (or (= c4 c_0) (= c4 c_1) (= c4 c_2)) (or (= c8 c_0) (= c8 c_1) (= c8 c_2)) (or (= c9 c_0) (= c9 c_1) (= c9 c_2)))))))))))
(check-sat)
(exit)
