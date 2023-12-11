# Pell's Equation
In [Freek's list of theorems](https://www.cs.ru.nl/~freek/100/), the existence of non-trivial solutions to Pell's equation $x^2-dy^2=1$ was previously resolved for $d$ of the form $d = a^2-1$.
In this work, we formalize the existence of non-trivial solutions to Pell's equation $x^2-dy^2=1$ in Lean in the most general setting - when $d$ is nonsquare.

Our formalization closely follows the proof using [Dirichlet's theorem on diophantine approximation](https://en.wikipedia.org/wiki/Dirichlet%27s_approximation_theorem). For example, see [this](https://imomath.com/index.cgi?page=ntPellsEquationSolutions).

## Contents
| No. | File               | Contents                                                                                                         |
|-----|--------------------|------------------------------------------------------------------------------------------------------------------|
| 1   | Theorem1           | Dirichlet's theorem (Lemma 1 [here](https://imomath.com/index.cgi?page=ntPellsEquationSolutions))                |
| 2   | Corollary2         | Descent step (Lemma 2 [here](https://imomath.com/index.cgi?page=ntPellsEquationSolutions))                       |
| 3   | Theorem3           | Existence of Solutions to Pell's (Theorem 3 [here](https://imomath.com/index.cgi?page=ntPellsEquationSolutions)])|
| 4   | Theorem4           | Characterization of Solutions to Pell's (WIP)                                                                    |
