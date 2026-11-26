G=/scratch/arthur/baguette-gate-20261124h; D=/scratch/arthur/scp-gcs-20261124
export CAKE_PB_CP=/cluster/arthur/cakepb-develop-cp-62bdc7f/cake_pb_cp E2E_TIMEOUT=100
[ $2 = e2e ] && export E2E_SOLVER=1
bash $G/tools/e2e/chain.sh $1 $D/oz-$2 2>&1 | tail -1
