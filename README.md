# Canonical-min

Canonical-min is a sound and complete solver for type inhabitation and unification in dependent type theory, written in 185 lines of Lean. Canonical-min serves as a simplified reference for the algorithm behind [Canonical](github.com/chasenorman/Canonical), and a baseline for the development of future automated reasoning tools. A special feature of this implementation is the use of the *continuation monad* to convert the type checker into a constraint solver. 

## Project Structure

- `Data.lean` — The definition of terms and types.
- `Monad.lean` — The monadic framework to convert the type checker into a solver.
- `Checker.lean` — The type checker.
- `Search.lean` — The iterative deepening depth-first search. 
