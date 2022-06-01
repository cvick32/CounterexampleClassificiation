#!/bin/zsh
git clean -Xf

if [[ "$(uname)" == "Darwin" ]]; then
    platform="Mac"
    sedi="-i.bak"
elif [[ "$(expr substr $(uname -s) 1 5)" == "Linux" ]]; then
    platform="Linux"
    sedi="-i"
fi


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
	power="aManInTheMiddle,bManInTheMiddle"
    fi
elif [[ "$2" == "default2" ]]
then
     power=""
else
    echo "Predicate set $2 not found"
    exit 1
fi

scope="$3"
redundancy="T"

if [[ "$1" == "sym" ]]
then
    prop="EventuallyAliceAndBobCommunicateWithEachOther"
    file="needhamSchroederSymmetric.als"
    args=($power $file $prop $scope $preds $redundancy)
elif [[ "$1" == "pub" ]]
then
    prop="EventuallyAliceAndBobCommunicateWithEachOther"
    file="needhamSchroederPublicKey.als"
    args=($power $file $prop $scope $preds $redundancy)
elif [[ "$1" == "pc" ]]
then
    prop="NeverSecretMessageEveCanSee"
    file="publicChannel.als"
    args=("empty" $file $prop $scope "relIsTrue,relEqualsMessage,relEqualsProcess,relEqualsKey" $redundancy)
elif [[ "$1" == "tcp" ]]
then
    if [[ "$2" == "all" ]]
    then
        preds="empty"
        power="AReadAttacker,BReadAttacker,relEqualsMessage,relAInState,relBInState,relNotEqualsTime"
    elif [[ "$2" == "default" ]]
    then
         preds="empty"
         power="AReadAttacker,BReadAttacker,relEqualsMessage,relAInState,relNotEqualsTime"
    elif [[ "$2" == "default2" ]]
    then
        preds="empty"
         power="AReadAttacker,BReadAttacker,relEqualsMessage,relAInState,relNotEqualsTime,attackerSentSyn,attackerSentSynAck"
    fi
    prop="NoHalfClosedConnectionEst"
    file="tcp.als"
    args=($preds $file $prop $scope $power $redundancy)
else
    echo "Experiment name $1 not found"
    exit 1
fi
echo "s/check Check${prop}.*/check Check${prop} for ${scope}/g" "./alloy/$file"
sed $sedi "s/check Check${prop}.*/check Check${prop} for ${scope}/g" "./alloy/$file"

javac -cp "./alloy/allAlloyChanges.jar:./src/" ./src/ClassifyCounterexamples.java
java -Xmx6g -cp "./alloy/allAlloyChanges.jar:./src/" ClassifyCounterexamples $args
