#!/bin/sh
NAME=$1 
COMMENTS=$(coqwc $NAME|awk 'FNR == 2{print $3}')
SPEC=$(coqwc $NAME|awk 'FNR == 2{print $1}')
RATIOCS=$(echo "scale=2; $COMMENTS/($SPEC+0.1)" | bc)
RATIOSC=$(echo "scale=2; $SPEC/($COMMENTS+0.1)" | bc)
echo "$COMMENTS\t$SPEC\t$RATIOCS\t$RATIOSC\t$NAME"