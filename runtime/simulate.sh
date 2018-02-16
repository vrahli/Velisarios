#!/bin/bash

sed -i '1iopen Prelude' pbft_simul.ml
ocamlfind ocamlc -package batteries -linkpkg Prelude.ml pbft_simul.mli pbft_simul.ml -o pbft_simul
./pbft_simul
