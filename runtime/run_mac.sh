#!/bin/bash
TERMINAL=gnome-terminal
CONF_FILE=config
NUM_REQUESTS=1000000
NUM_FAULTS=1
NUM_CLIENTS=1
PRINTING_PERIOD=100
PLOTTING_PERIOD=100

SIM_FILE=PBFTsim_mac.v

NUM_REPLICAS=$(( (3*${NUM_FAULTS})+1 ))
NUM_REPLICASM1=$(( ${NUM_REPLICAS}-1 ))
NUM_CLIENTSM1=$(( ${NUM_CLIENTS}-1 ))


# Sets number of faults and clients
sed -i -- "s/Definition F := [0-9]*/Definition F := ${NUM_FAULTS}/g"    ${SIM_FILE} 
sed -i -- "s/Definition C := [0-9]*/Definition C := ${NUM_CLIENTSM1}/g" ${SIM_FILE}


# Extraction
make sext


# Compile OCaml files
make


# Replica keys
for i in `seq 0 ${NUM_REPLICASM1}`;
do
    for j in `seq 0 ${NUM_REPLICASM1}`;
    do
	./MacKey.native -sym symmetric_key${i}-${j} -symsrc ${i} -symdst ${j} -print false
    done
done    


# Client keys
for i in `seq 0 ${NUM_REPLICASM1}`;
do
    for j in `seq 0 ${NUM_CLIENTSM1}`;
    do
	./MacKey.native -sym symmetric_key_client${i}-${j} -symsrc ${i} -symdst ${j} -print false
    done
done    


# Replicas
for i in `seq 0 ${NUM_REPLICASM1}`;
do
    ${TERMINAL} --title=replica${i} --geometry 60x20+$(( 100*(${i}+1) ))+$(( 100*(${i}+1) )) -x ./Replica.native -id ${i} -num-faults ${NUM_FAULTS} -num-clients ${NUM_CLIENTS} -conf ${CONF_FILE}
done    


sleep 2


# Clients
for i in `seq 0 ${NUM_CLIENTSM1}`;
do
    ${TERMINAL} --title=client${i} --geometry 150x40+$(( 500+(100*(${i}+1)) ))+$(( 100*(${i}+1) )) -x ./Client_mac.native -id ${i} -max ${NUM_REQUESTS} -num-faults ${NUM_FAULTS} -printing-period ${PRINTING_PERIOD} -plotting-period ${PLOTTING_PERIOD} -conf ${CONF_FILE}
done    
