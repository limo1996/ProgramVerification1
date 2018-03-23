
### Tseitin CNF conversion vs. Disjunction distribution

Firstly we implemented tseitin CNF conversion and used it for converting formulas into CNF format. 
However, during implementation of sudoku it turned out that tseitin conversion is not efficient for this type of problem because it introduces many variables. 
While in theory tseitin conversion does not introduce computing overhead, in reality it does.
Difficulty of formula in term of decisions is not increaded by tseitin because it introduces many variables which are tightly correlated. 
However this correlation causes meny consequent unit propagations which in case of wrong decision need to be undone. 
This step causes huge overhead that causes that formula is not solvable in reasonable time while in disjunction distribution case it takes no more than 10 seconds for easy and medium problems and up to 20 seconds for difficult ones. 

As consequence we wanted to see performance of both techniques in terms of formula conversion and consequent performance of solvers over converted formula.
Following table shows average performance of these techniques in formula conversion.

| Conversion        | Dis. distribution  | Tseitin  |
| ----------------- |:------------------:| --------:|
| 100 Random tests  | 12.5532            | 9.2112   |
| 100 Exhaustive    | 3.2045             | 2.4605   |

We can see that tseitin conversion is quite faster. 
