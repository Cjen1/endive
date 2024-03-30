#!/bin/bash
#SBATCH -J AsyncRaft_endive_Job               # Job name
#SBATCH --partition short    # Partition name
#SBATCH --time=16:00:00       # Time limit.
#SBATCH --constraint="[broadwell|cascadelake]"       # Newer processors.
#SBATCH -N 1                   # Number of nodes
#SBATCH -n 1                   # Number of tasks
#SBATCH --cpus-per-task 28                  # Number of cores

specname="AsyncRaft"
lscpu # log CPU info.
module load OpenJDK/19.0.1
mkdir -p benchmarking
cd benchmarking
mkdir -p $specname
cd $specname
# Clone if not already cloned.
git clone -b ind-tree https://github.com/will62794/endive.git
cd endive
git pull --rebase

for seed in 2
do

tlc_workers=24
num_cti_workers=8
nrounds=45
ninvs=40000
max_num_ctis_per_round=2000
target_sample_states=200000
num_simulate_traces=200000


common_flags=" --seed $seed --tlc_workers $tlc_workers --override_num_cti_workers $num_cti_workers"
common_flags+=" --debug --target_sample_time_limit_ms 10000 --num_simulate_traces $num_simulate_traces --target_sample_states $target_sample_states"
common_flags+=" --opt_quant_minimize --k_cti_induction_depth 1"
common_flags+=" --ninvs $ninvs --max_num_ctis_per_round $max_num_ctis_per_round"
common_flags+=" --save_dot --max_num_conjuncts_per_round 16 --niters 4 --nrounds $nrounds"

srun -o /home/schultz.w/endive_logs/${specname}/${specname}_output_%j_${seed}.txt \
    python3 endive.py --spec benchmarks/$specname \
    $common_flags --auto_lemma_action_decomposition --enable_partitioned_state_caching --proof_tree_mode 

# srun -o /home/schultz.w/endive_logs/${specname}_baseline/${specname}_baseline_output_%j_${seed}.txt \
#     python3 endive.py --spec benchmarks/$specname \
#     $common_flags 

done


    # --action_filter "ClientRequestAction,AdvanceCommitIndexAction,AcceptAppendEntriesRequestLearnCommitAction,AcceptAppendEntriesRequestAppendAction,HandleAppendEntriesResponseAction"
