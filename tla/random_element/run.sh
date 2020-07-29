#!/bin/bash

echo "Runs specs with simulation mode until 100000 behaviours have been generated."
echo "Each behaviour is either completed, or not completed."
echo "Improper use of RandomElement can cause behaviours to terminate before successfully completing"
echo ""

echo "---------------------------------------------------------------------"
echo "SINGLE VARIABLE TEST ----------------------------------------"
echo "SIMULATION MODE WITH NON-DETERMINISM"
bash test-simulate.sh test_non_det.tla test.cfg 100000 test_non_det.log 1

echo ""
echo "SIMULATION MODE WITH RandomElement"
bash test-simulate.sh test_random_element.tla test.cfg 100000 test_random_element.log 1

echo ""
echo "---------------------------------------------------------------------"
echo "TWO DEPENDENT VARIABLES TEST ----------------------------------------"
echo "SIMULATION MODE WITH NON-DETERMINISM"
bash test-simulate.sh test_dependent_vars_non_det.tla test_dependent_vars.cfg 100000 test_dependent_vars_non_det.log 1

echo ""
echo "SIMULATION MODE WITH RandomElement"
bash test-simulate.sh test_dependent_vars_random_element.tla test_dependent_vars.cfg 100000 test_dependent_vars_random_element.log 1