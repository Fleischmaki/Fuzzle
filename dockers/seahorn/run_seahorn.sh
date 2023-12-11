#!/bin/bash

# Arg1: Target Source code
# Arg2: Timeout (in minutes)

WORKDIR=/home/usea/workspace

INDIR=$WORKDIR/inputs
OUTDIR=$WORKDIR/outputs
OUTFILE=$OUTDIR/res

mkdir -p $OUTDIR

# Remove explicit initialisations
# sed -i "s/init(.*);//g" $1 
# sed -i "s/ = __VERIFIER_nondet_.*()//g" $1

# Create dummy file to indicate running start
touch $WORKDIR/.start
timeout $2s sea $3 -m=64 -unroll-threshold=1024 ${@:4} $1 &> $OUTFILE
touch $WORKDIR/.end