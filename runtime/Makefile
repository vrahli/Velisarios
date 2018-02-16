default: Replica.native Client.native Client_mac.native RsaKey.native MacKey.native Simul.native

Replica.native: Replica.ml
	ocamlbuild -tag thread -use-ocamlfind -package ppx_jane,async,core_extended,batteries,rpc_parallel,nocrypto.unix Replica.native

Client.native: Client.ml
	ocamlbuild -tag thread -use-ocamlfind -package ppx_jane,async,core_extended,batteries,rpc_parallel,nocrypto.unix Client.native

Client_mac.native: Client_mac.ml
	ocamlbuild -tag thread -use-ocamlfind -package ppx_jane,async,core_extended,batteries,rpc_parallel,nocrypto.unix Client_mac.native

RsaKey.native: RsaKey.ml
	ocamlbuild -tag thread -use-ocamlfind -package ppx_jane,async,core_extended,batteries,rpc_parallel,nocrypto.unix RsaKey.native

MacKey.native: MacKey.ml
	ocamlbuild -tag thread -use-ocamlfind -package ppx_jane,async,core_extended,batteries,rpc_parallel,nocrypto.unix MacKey.native

Simul.native: Simul.ml
	ocamlbuild -tag thread -use-ocamlfind -package ppx_jane,async,core_extended,batteries,rpc_parallel,nocrypto.unix Simul.native

Test.native: Test.ml
	ocamlbuild -tag thread -use-ocamlfind -package ppx_jane,async,core_extended,batteries,rpc_parallel,nocrypto.unix Test.native

TestServer.native: TestServer.ml
	ocamlbuild -tag thread -use-ocamlfind -package ppx_jane,async,core_extended,batteries,rpc_parallel,nocrypto.unix TestServer.native

TestClient.native: TestClient.ml
	ocamlbuild -tag thread -use-ocamlfind -package ppx_jane,async,core_extended,batteries,rpc_parallel,nocrypto.unix TestClient.native

ext:
	(cd ..; make PBFT/PBFT.vo)
	(cd ..; make PBFT/PBFTcollision_resistant.vo)
	coqc -R ../coq-tools util -R ../model model -R ../PBFT PBFT -R ../PrimaryBackup PrimaryBackup -R ../runtime runtime -R ../TwoThirds TwoThirds Simulator.v
	coqc -R ../coq-tools util -R ../model model -R ../PBFT PBFT -R ../PrimaryBackup PrimaryBackup -R ../runtime runtime -R ../TwoThirds TwoThirds PBFTsim.v

sext:
	(cd ..; make PBFT/PBFT.vo)
	(cd ..; make PBFT/PBFTcollision_resistant.vo)
	coqc -R ../coq-tools util -R ../model model -R ../PBFT PBFT -R ../PrimaryBackup PrimaryBackup -R ../runtime runtime -R ../TwoThirds TwoThirds Simulator.v
	coqc -R ../coq-tools util -R ../model model -R ../PBFT PBFT -R ../PrimaryBackup PrimaryBackup -R ../runtime runtime -R ../TwoThirds TwoThirds PBFTsim_mac.v

oldext:
	coqc -R ../coq-tools util -R ../model model -R ../PBFT PBFT -R ../PrimaryBackup PrimaryBackup -R ../runtime runtime -R ../TwoThirds TwoThirds PBFTsim.v

clean:
	rm -f *.cmo
	rm -f *.cmi
	rm -f *.cma
	rm -f *.native
	rm -f *.byte
	rm -f a.out
	rm -Rf _build
	rm -f PbftReplica*
	rm -f *.glob
	rm -f *.vo
	rm -f .*.aux
	rm -f *.dat
	rm -f private_key*
	rm -f public_key*
