Compilation
===========

The code compiles with Coq version 8.9.0.  To compile the code, first
generate a Makefile by running `./create-makefile.sh`.  Then type
`make -j X`, where X is the number of jobs you want to use.

Note that create-makefile.sh requires a version of base >= 4.



Roadmap
=======

- The model is in `model`.
- Our formalization of PBFT is in `PBFT`.
- Our runtime environment is in `runtime`.



Running
=======

To run PBFT, check out `runtime/README.md`.
