#!/bin/zsh
# usage: run_scale.sh "<m list>" <seconds per run> <rss cap MB> <log> "<k list>" <hh|sq>
# One run at a time on one core; a run past the time or memory cap ends the loop for that m.
PY=${PY:-python3}
for m in ${=1}; do
  for k in ${=5:-2 3 4 5 6 7 8}; do
    fail=0
    for seed in 0 1 2; do
      OMP_NUM_THREADS=1 nice -n 15 perl -e "alarm $2; exec @ARGV" $PY -I probe.py $k $m $seed ${6:-hh} >> $4 2>/dev/null &
      pid=$!
      while kill -0 $pid 2>/dev/null; do
        r=$(ps -o rss= -p $pid 2>/dev/null | tr -d ' ')
        if [[ -n $r && $r -gt $(( $3 * 1024 )) ]]; then kill $pid; echo "k=$k m=$m seed=$seed RSS_CAP" >> $4; fi
        sleep 2
      done
      wait $pid; s=$?
      [[ $s -ne 0 ]] && { echo "k=$k m=$m seed=$seed stopped exit=$s" >> $4; fail=1; break; }
    done
    [[ $fail -eq 1 ]] && break
  done
done
