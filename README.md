# INF: QBF solver

This repository contains my Bachelor's Thesis in Computer Engineering in the specialization of 
Computation. The developed software includes: 

- QDIMACS parsers: a more complete one that can be used to verify if an instance is correctly 
    represented (not thoroughly tested); and a simpler and more efficient one that presumes that
    instances are correct (used by the implemented solvers).
- A simple CNF (Conjunction Normal Form) preprocessor for quantified formulas (in Prenex Normal Form)
- Naive QBF (Quantified Boolean Formula) solver
- INF solver, another QBF solver based on a more sophisticated algorithm

They have been implemented in Python, since the primary goal of the project was to get in touch with
the QBF problem, and see if the INF solver's algorithm outstands the Naive approach. Both of them 
have been compared to DepQBF, a state of the art solver.

---

## Structure

- In the `src` folder we find all the aforementioned software, the main part of the project. All of these
    files are thoughtfully commented, so there is no a big necessity to read the memory of the work to
    understand the major part of the implementation.
- In the `tests` folder we have some simple tests of the principal functions in `src`. The most superficial
    tests that were written during the development have been removed. Only the most interesting ones remain
    here. We have a file that compares different implementations of the regularization transformation too.
- In the `data` folder, we have the QDIMACS and DIMACS instances used to benchmark and test the solvers.
    The instances that have been used are uncompressed, but some extra instances (that might be too big 
    for both prototypes of the Naive and INF solvers) have been included in three compressed files. With
    them, a file that lists some interesting links is included too.
- In the `benchmark_results` folder we can find the principal script that was used to obtain the information
    about the execution of the solvers on the previously mentioned instances: memory use, CPU and wall or
    real time, statistics about the instances themselves, and so on. We have results per instance for all
    the solvers mentioned above, an aggregation of those results, and a final summary of the most 
    interesting aggregate data. In the subfolders we have included the simple scripts that were used to 
    obtain the following data:

    - In `plots` we can visualize the obtained results with some barplots and performance-profiles or 
        cactus-plots.
    - In `inf_iterative_experimentation` we have the summarized results that we have obtained when improving
        the INF solver iteratively, with a JSON with comments file that lists the implemented changes.
    - In `compare_naive_fni` we see which instances are better solved by the Naive solver compared to the
        INF one, and viceversa.

---

## Use

Clone the repository to have a copy of the source code of the implementations of the QBF solvers and the 
instances to perform the tests on. To execute the tests, you have to be located in the source folder of the
project, and execute them as modules. For example:

```bash
python3 -m tests.test_inf
```

To execute the benchmarking script we have to do the same:

```bash
python3 -m benchmark_results.benchmark_script
```

The other simpler scripts that are stored in the subfolders of `benchmark_results` can be executed 
directly from the folders that contain them (and should be, due to relative paths of the `csv` files 
with the data about the results that they use). For example, in the `benchmark_results/plots` folder:

```bash
python3 create_plots.py
```
