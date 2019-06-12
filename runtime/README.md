=====================================================================
=--

We use Async to implement sender/receiver threads, and
[Nocrypto](http://mirleft.github.io/ocaml-nocrypto/doc/index.html) for
crypto stuff.  To install all that, run:

- opam repo add janestreet https://ocaml.janestreet.com/opam-repository
- opam install async ppx_jane core_extended rpc_parallel batteries cppo_ocamlbuild nocrypto


=====================================================================
=--

To use the simulator:

- run "make ext" and then "make"
- run "./Simul.native -max XXX", where XXX is the number of requests
  to send

By default it's going to sign messages using RSA. If you don't want to
use signatures, set 'signing' to false in Simul.ml and comment out the
crypto stuff towards the end of PBFTsim.v (see the comments
there---search for "crypto stuff").

=====================================================================
=--

To use the runtime environment:

- run: ./run.sh

- Clients will produce data files (pbftX.dat) that can be plotted using:
    cp pbft_ts_X_R_C.dat pbft.dat; gnuplot script.p
    cp pbft_avg_X_R_C.dat pbft.dat; gnuplot script.p
  where X is the client id
        R is the number of replicas
	C is the number of clients
