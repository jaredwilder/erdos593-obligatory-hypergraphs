#!/bin/bash
export PATH=/root/.elan/bin:$PATH
LP=$(cd /root/formalizer/proofs && lake env printenv LEAN_PATH)
export LEAN_PATH="$LP:/root/e593/build"
mkdir -p /root/e593/build
cd /root/e593
f=$1
nice -n 19 taskset -c 2,3 lean -o /root/e593/build/$f.olean /root/e593/$f.lean > /root/e593/$f.log 2>&1
echo "EXIT=$?"
