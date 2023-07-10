# README #

### How to set it up? ###

* Install ocaml
* Install dune
* Install cameleer
* Install why3
* Install provers (alt ergo, z3 etc.)
* Install OUnit2

### How to run cameleer? ###

* In the Lib directory, run cameleer using "cameleer -L . *filename*.ml"
* Once why3 opens, run the provers (using the key "3" in the functions)

### How to run tests? ###

* In the OUnit directory, run "dune build ./*filename*.ml" and then "dune exec ./*filename*.exe
* Console will give the output relative to the test results
