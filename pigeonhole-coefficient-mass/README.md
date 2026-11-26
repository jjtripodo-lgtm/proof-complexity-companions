# Pigeonhole coefficient mass

Companion to John Tripodo, *How many pigeons make a refutation cheap? A coefficient-mass dichotomy for the plain pigeonhole principle*.

The manuscript addresses the bounded-versus-diverging pigeon-to-hole ratio and the effect of functionality in Section 4, Question 1 of Potechin and Zhang (ICALP 2024). These scripts check finite arithmetic and small boards. The asymptotic theorems are proved in the manuscript and the main claims are kernel-checked in the [Lean project](lean/).

## Rational block and Table 1

Run with standard-library Python:

```sh
python3 verify_block.py
```

This checks all 357,911 allowed boxes and integrates the four dual values over the rationals. It rounds only the reported logarithms and rates.

## Exact small-board linear programs

The recorded run used Python with NumPy 2.3.5, SciPy 1.17.0, and SymPy 1.14.0:

```sh
python3 -m pip install numpy==2.3.5 scipy==1.17.0 sympy==1.14.0
python3 php_exact_lp.py > replay.json
diff -u php_exact_lp.json replay.json
```

HiGHS proposes primal and dual witnesses. The script checks both witnesses and their equal objectives in integer arithmetic for 17 cases, including full Boolean boards and the restricted partial-matching domain. A solver upgrade can select different witnesses with the same exact objective; the JSON also records the witness support counts.

[ICALP 2024 paper](https://doi.org/10.4230/LIPIcs.ICALP.2024.117)
