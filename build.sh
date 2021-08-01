#!/bin/zsh
git clean -Xf

if [[ "$2" == "default" ]]
then
    power="empty"
    preds="relEqualsMessage,relEqualsProcess,relKeyinKey,relHappensBefore,relNonceInNonce"
elif [[ "$2" == "all" ]] 
then
    preds="relEqualsMessage,relEqualsProcess,relKeyinKey,relHappensBefore,aManInTheMiddle,bManInTheMiddle,relReplay,relNonceInNonce"
    if [[ "$1" == "sym" ]]
    then
	power="relReplay"
    elif [[ "$1" == "pub" ]]
    then
	power="manInTheMiddleConstraint"
    fi
else
    echo "Predicate set $2 not found"
    exit 1
fi  



if [[ "$1" == "sym" ]]
then 
    args=($power "needhamSchroederSymmetric.als" "EventuallyAliceAndBobCommunicateWithEachOther" "$3" $preds)
elif [[ "$1" == "pub" ]]
then 
    args=($power "needhamSchroederPublicKey.als" "EventuallyAliceAndBobCommunicateWithEachOther" "$3" $preds)
elif [[ "$1" == "pc" ]] 
then
    args=("empty" "publicChannel.als" "NeverSecretMessageEveCanSee" "$3" "relIsTrue,relEqualsMessage,relEqualsProcess,relEqualsKey")
else 
    echo "Experiment name $1 not found"
    exit 1
fi  


javac -cp "./alloy/allAlloyChanges.jar:./src/" ./src/ClassifyCounterexamples.java
java -Xmx6g -cp "./alloy/allAlloyChanges.jar:./src/" ClassifyCounterexamples $args
