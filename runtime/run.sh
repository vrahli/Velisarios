#!/bin/bash
TERMINAL=gnome-terminal
CONF_FILE=config
NUM_REQUESTS=10000
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
make ext


# Compile OCaml files
make


echo "Generating keys"
# Replica keys
for i in `seq 0 ${NUM_REPLICASM1}`;
do
    ./RsaKey.native -priv private_key${i} -pub public_key${i} -print false
done    


# Client keys
for i in `seq 0 ${NUM_CLIENTSM1}`;
do
    ./RsaKey.native -priv private_key_client${i} -pub public_key_client${i} -print false
done    


# Replicas
for i in `seq 0 ${NUM_REPLICASM1}`;
do
    ${TERMINAL} --title=replica${i} --geometry 60x20+$(( 100*(${i}+1) ))+$(( 100*(${i}+1) )) -- ./Replica.native -id ${i} -num-faults ${NUM_FAULTS} -num-clients ${NUM_CLIENTS} -conf ${CONF_FILE}
done    


sleep 2


# Clients
for i in `seq 0 ${NUM_CLIENTSM1}`;
do
    ${TERMINAL} --title=client${i} --geometry 150x40+$(( 500+(100*(${i}+1)) ))+$(( 100*(${i}+1) )) -- ./Client.native -id ${i} -max ${NUM_REQUESTS} -num-faults ${NUM_FAULTS} -printing-period ${PRINTING_PERIOD} -plotting-period ${PLOTTING_PERIOD} -conf ${CONF_FILE}
done    
