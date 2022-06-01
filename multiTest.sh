#!/bin/zsh

for exp in "sym" "pub" "tcp"
do
  if [[ $exp == "sym" ]]
  then
    range=(10 15 20 25)
    dir="./experiments/NSSymmetricTests"
    file="needhamSchroederSymmetricClassification.als"
  elif [[ $exp == "pub" ]]
  then
    range=(10 15 20 25)
    dir="./experiments/NSPublicKeyTests"
    file="needhamSchroederPublicKeyClassification.als"
  elif [[ $exp == "tcp" ]]
  then
      range=(7 8 9 10)
      dir="./experiments/TCPTests"
      file="tcpClassification.als"
  fi
  for pred in "default" "all"
  do
    mkdir $dir/$pred/
    for scope in ${range[@]}
    do
	for x in 1
	do
	    echo "$exp $pred $scope $x"
	    t="${exp}${pred}b${scope}run${x}"
	    mkdir $dir/$pred/$t
	    time ./build.sh $exp $pred $scope > $dir/$pred/$t/log.txt
	    mv ./alloy/$file $dir/$pred/$t/classification.als
	    echo $t
	done
    done
  done
done
