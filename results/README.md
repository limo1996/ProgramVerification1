
## CNF Conversion

CNF conversion is implemented in two files: CNF.scala (tseitin part) and CNFConverter.scala (all other parts as static methods). 

### Tseitin CNF conversion vs. Disjunction distribution

Firstly we implemented tseitin CNF conversion and used it for converting formulas into CNF format. 
However, during implementation of sudoku it turned out that tseitin conversion is not efficient for this type of problem because it introduces many variables. 
While in theory tseitin conversion does not introduce computing overhead, in reality it does.
Difficulty of formula in term of decisions is not increaded by tseitin because it introduces many variables which are tightly correlated. 
However this correlation causes meny consequent unit propagations which in case of wrong decision need to be undone. 
This step causes huge overhead that causes that formula is not solvable in reasonable time while in disjunction distribution case it takes no more than 10 seconds for easy and medium problems and up to 20 seconds for difficult ones. 

As consequence we wanted to see performance of both techniques in terms of formula conversion and consequent performance of solvers over converted formula.
Following table shows average performance of these techniques in formula conversion.

| Conversion        | Dis. distribution   | Tseitin   |
| ----------------- |:-------------------:| ---------:|
| 100 Random tests  | 12.5532s            | 9.2112s   |
| 100 Exhaustive    | 3.2045s             | 2.4605s   |

We can see that tseitin conversion is quite faster. 


## Sudoku

We also implemented bonus task - sudoku by encoding mechanism described in [paper](https://pdfs.semanticscholar.org/535d/06391275618a7b913d1c98a1353286db8d74.pdf) written by Inês Lynce and Jöel Ouaknine. They presented two approaches but we picked minimal encoding that looked more readable to us. All tests even the hardest ones are able to finish within 30 seconds with CDCLBaseline solver. We did not try other solvers since CDCL is clearly faster than DPLL on structured tests.

### Sudoku performance

After successful validation of our sudoku implementation we have decided to test the performance of selected solver configurations. It turned out that there is no clear winner. Formula is in every sudoku almost identical except the conjoined literals that are part of initial number distribution over grid. It is interesting to see that these small modifications caused different performances of solvers. We have picked few represenatives that represent patterns that repeat in results. Two most common patterns are where DPLL Baseline is much faster than others (sudoku 9 and 10) and pattern where DPLL Baseline is much slower than other three (suduko 35 and 38). 

| Sudoku test        | DPLL Baseline   | DPLL Without Pure   | CDCL Baseline | CDCL Without Learning |
| ------------------ |:---------------:| ------------------:|:-------------:|:----------------------:|
| sudoku9.txt        | 3224.4s         | 5150.2s            | 6039.8s       | 5445.6s                |
| sudoku10.txt       | 2222.6s         | 2812.8s            | 2745.2s       | 2799.2s                |
| sudoku35.txt       | 1780.0s         | 1127.0s            | 1016.6s       | 1162.2s                |
| sudoku38.txt       | 1507.8s         | 1094.4s            | 1082.4s       | 1063.0s                |
| sudoku5.txt        | 1057.2s         | 1110.8s            | 1091.4s       | 1430.6s                |
| sudoku11.txt       | 1100.8s         | 2133.2s            | 1221.8s       | 1193.4s                |
| sudoku13.txt       | 1290.2s         | 1314.0s            | 1400.4s       | 1350.4s                |
| sudoku3.txt        | 1368.4s         | 1436.8s            | 1456.8s       | 1445.8s                |

