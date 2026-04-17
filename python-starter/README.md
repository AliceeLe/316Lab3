# 15-316 Lab 3 - Python

If you have any questions, please post on Piazza or come to office hours.

## Environment Setup

Clone this repository onto your local machine or your Andrew home directory.

You will need to use Python 3.10 to complete this lab. We encourage you to set up a fresh virtual environment before continuing.

* Create a new conda environment.
```
$ conda create -n py310 python=3.10
```
This may not work if you are using a version of `conda` prior to 4.11. If you do not have `conda`, or need to upgrade, you can [download the latest installer](https://docs.conda.io/en/latest/miniconda.html). If you already have a recent version on your system, but not Python 3.10, then you can run:
```
$ conda install -c conda-forge python=3.10
```
After installing Python 3.10 (or if you already have it), create a new environment as described above. You can use the environment by running:
```
$ conda activate py310
```
In the new environment, install the necessary packages.
```
(py310)$ pip install -r requirements.txt
```

## Building

To build the project, run the following command:
```bash
make
```

This will build the project and create `pca_serve` binaries in your current directory.

To clean the project directory, run the following command:
```bash
make clean
```

## Handin

To create a `lab3.zip` file for handin, run the following command:
```bash
make handin
```

## Getting Started

You will not need to worry about handling the CLI arguments, parsing, printing out the correct messages, or exiting with the correct error codes. This is all done for you already, and you will only need to implement the core logic for each part of the project.

### Starter Code

These are the interfaces you will be working with:
- [`src/pca_logic.py`](src/pca_logic.py): The abstract syntax trees (AST) for PCA policies and proofs.
  - This contains the types that represent formulas and proofs, and some utility functions for printing the AST.

These are the files that you will need to modify:
- [`src/utils.py`](src/utils.py): Substitution and equality helper functions that you need to implement.
- [`src/verify.py`](src/verify.py): Code to check whether signatures are well-formed and proofs are correct.
