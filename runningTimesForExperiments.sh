#!/bin/zsh
for exp in "NSSymmetricTests" "NSPublicKeyTests" "TCPTests"; do
  for pred in "all" "default"; do
    echo "------ $exp $pred ------"
    for filename in ./experiments/$exp/$pred/*/log.txt; do
      echo "$filename"
      python3 total_running_time.py "$filename"
    done
  done
done
