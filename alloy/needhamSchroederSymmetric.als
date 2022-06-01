open util/ordering[Time] as TO
sig Time { }

abstract sig Key {}
abstract sig Principal {
	knows: set Nonce -> Time,
	message: Message lone -> Time
} 

abstract sig Nonce {}

one sig AliceNonce, BobNonce, EveNonce, BreakNonce extends Nonce {}

one sig Server extends Principal {} 

one sig Key_AS, Key_BS, Key_AB extends Key {}

one sig Message {
	sender: Principal lone -> Time, 
	nonce: Nonce lone -> Time,
	process: Process lone -> Time,
	key: Key lone -> Time, 
	encryption: Key lone -> Time,
	inner_key: Key lone -> Time,
	inner_process: Process lone -> Time,
	inner_encryption: Key lone -> Time
}

abstract sig Process extends Principal {
	comm_key: Key lone -> Time,
	nonce: one Nonce,
	keys: set Key -> Time
}

one sig Eve extends Process {}

one sig Alice, Bob extends Process {} {
	no keys
}

fun dec (i: Int): Int {
	i - 1
}

pred init (t: Time) {
	Alice.nonce = AliceNonce
	Bob.nonce = BobNonce
	Eve.nonce = EveNonce
	Alice.knows.t = Alice.nonce
	Bob.knows.t = Bob.nonce
	Message.sender.t = Server
	Message.encryption.t = Key_AS
	Message.inner_key.t = Key_AS
	some Alice.message.t
	no Alice.comm_key.t
	no Bob.comm_key.t
	no Eve.keys.t
}

pred AliceCommWithServer(t, t': Time) {
	Alice.message.t.sender.t = Server
	Alice.message.t.encryption.t = Key_AS
	Alice.message.t.inner_key.t = Key_AS
	let serverMsg = Server.message.t' | 
		(serverMsg.sender.t' = Alice and
		serverMsg.nonce.t' = Alice.nonce and
		serverMsg.process.t' = Bob and
		no serverMsg.key.t' and
		serverMsg.encryption.t' = Key_AS and
		no serverMsg.inner_key.t' and
		no serverMsg.inner_process.t' and
		no serverMsg.inner_encryption.t')
	noServerChange[t, t']
	noProcChange[t, t', Bob]
	noProcChange[t, t', Alice]
	Eve.keys.t' = Eve.keys.t
}

pred ServerCommWithAlice(t, t': Time) {
	Server.message.t.sender.t = Alice
	let aliceMsg = Alice.message.t' | 
		(aliceMsg.sender.t' = Server and
		aliceMsg.nonce.t' = Server.message.t.nonce.t and
		aliceMsg.process.t' = Server.message.t.process.t and
		aliceMsg.key.t' = Key_AB and
		aliceMsg.encryption.t' = Key_AS and
		aliceMsg.inner_key.t' = Key_AB and 
		aliceMsg.inner_process.t' = Bob and
		aliceMsg.inner_encryption.t' = Key_BS)
	Alice.comm_key.t' = Alice.message.t'.key.t'
	Alice.knows.t' = Alice.knows.t
	noServerChange[t, t'] 
	noProcChange [t, t', Bob]
	Eve.keys.t' = Eve.keys.t
}

pred AliceSendToBob (t, t': Time) {
	Alice.message.t.inner_encryption.t = Key_BS
	let bobMsg = Bob.message.t' |
		(bobMsg.sender.t' = Alice and
		no bobMsg.nonce.t' and
		bobMsg.process.t' = Alice.message.t.inner_process.t and		
		bobMsg.key.t' = Alice.message.t.inner_key.t and
		bobMsg.encryption.t' = Alice.message.t.inner_encryption.t and
		no bobMsg.inner_key.t' and
		no bobMsg.inner_process.t' and
		no bobMsg.inner_encryption.t')
	Bob.comm_key.t' = Bob.message.t'.key.t'
	Bob.knows.t' = Bob.knows.t 
	Eve.keys.t' = Bob.comm_key.t' + Eve.keys.t
	noProcChange[t, t', Alice]
	noServerChange[t, t']
}

pred BobSendNonce (t, t': Time) {
	some Bob.message.t
	some Bob.comm_key.t
	Bob.knows.t' = Bob.knows.t + Bob.message.t.nonce.t
	let newMsg = Bob.message.t.sender.t.message.t' |
		(newMsg.sender.t' = Bob and
		newMsg.nonce.t' = Bob.nonce and
		no newMsg.process.t' and
		no newMsg.key.t' and
		newMsg.encryption.t' = Bob.comm_key.t and
		no newMsg.inner_key.t' and
		no newMsg.inner_process.t' and
		no newMsg.inner_encryption.t')
	noProcChange[t, t', Alice]
	Bob.comm_key.t' = Bob.comm_key.t
	noServerChange[t, t']
	Eve.keys.t' = Eve.keys.t
}

pred AliceSendNonce (t, t': Time) {
	Alice.message.t.sender.t = Bob
	some Alice.message.t.nonce.t
	some Alice.comm_key.t
	Alice.knows.t' = Alice.knows.t + Alice.message.t.nonce.t
	let newMsg = Alice.message.t.sender.t.message.t' | 
		(newMsg.sender.t' = Alice and
		newMsg.nonce.t' = BreakNonce and
		no newMsg.process.t' and
		no newMsg.key.t' and
		newMsg.encryption.t' = Alice.comm_key.t and
		no newMsg.inner_key.t' and
		no newMsg.inner_process.t' and
		no newMsg.inner_encryption.t')
	noServerChange[t, t']
	Alice.comm_key.t' = Alice.comm_key.t
	noProcChange[t, t', Bob]
}

pred AttackerSendMessage (t, t': Time) {
	some Eve.keys.t // assumes we broke encryption
	some Bob.comm_key.t
	some Alice.comm_key.t
	Bob.message.t.nonce.t = BreakNonce
	let bobMsg = Bob.message.t' |
		(bobMsg.sender.t' = Eve and
		bobMsg.nonce.t' = Eve.nonce and
		bobMsg.process.t' = Alice and		
		no bobMsg.key.t' and
		bobMsg.encryption.t' = Key_AB and // assumes we broke encryption
		no bobMsg.inner_key.t' and
		no bobMsg.inner_process.t' and
		no bobMsg.inner_encryption.t')
	noServerChange[t, t']
	noProcChange[t, t', Alice]
	noProcChange[t, t', Bob]
}

pred StealAliceKey (t, t': Time) {
	Key_AS in Eve.keys.t
	Alice.knows.t' = Alice.knows.t + Eve.nonce
}

pred StealBobKey (t, t': Time) {
	Key_BS in Eve.keys.t
	Bob.knows.t' = Bob.knows.t + Eve.nonce
}

pred noServerChange (t, t': Time) {
	Server.knows.t = Server.knows.t'
}

pred noProcChange (t, t': Time, p: Process) {
	p.comm_key.t = p.comm_key.t'
	p.knows.t = p.knows.t'
}

fact Traces {
	first.init
	all t: Time - last | let t' = t.next |
		AliceCommWithServer[t, t'] 
		or ServerCommWithAlice[t, t']
		or AliceSendToBob[t, t']
		or BobSendNonce[t, t']
		or AliceSendNonce[t, t']
		or AttackerSendMessage[t, t']
		or StealAliceKey[t, t']
		or StealBobKey[t, t']
}

fact alwaysDifferentSender {
	all t: Time, t': t.next | Message.sender.t != Message.sender.t'
}

fact onlyOneMessagePerPrincipal {
	all t: Time {
 		some p: Principal {
			some p.message.t && no (Principal - p).message.t
		}
	}
}


fact attackerFrame {
	all t: Time, t': t.next | no Eve.message.t implies Eve.knows.t' = Eve.knows.t 
}

pred relHappensBefore (t: Time, t': Time) {
	t.lt[t']
}


pred relReplay[t,t': Time] {
    relHappensBefore[t, t']
    Message.sender.t' != Message.sender.t
    Message.nonce.t' = Message.nonce.t 
    Message.process.t' = Message.process.t 
    Message.key.t' = Message.key.t 
    Message.encryption.t' = Message.key.t 
    Message.inner_key.t' = Message.inner_key.t 
    Message.inner_process.t' = Message.inner_process.t 
    Message.inner_encryption.t' = Message.inner_encryption.t 
}

pred relKeyinKey [k1, k2: Key] {
	k1 in k2
}

pred relEqualsKey[x: Key, y: Key] {
	x = y
}

pred relEqualsMessage[x: Message, y: Message] {
	x = y
}

pred relEqualsProcess[x: Process, y: Process] {
	x = y
}

pred relNotEqualsTime[x: Time, y: Time] {
	!(x = y)
}

pred relNonceInNonce[n1, n2: Nonce] {
	n1 in n2
}

/*
classification by hand
pred characterize_EveStealsAServerKey {
	some t: Time {
		Key_AS in Eve.keys.t
	}
		
}  fact { !characterize_EveStealsAServerKey }

pred characterize_EveStealsBServerKey {
	some t: Time {
		Key_BS in Eve.keys.t
	}
		
}  fact { !characterize_EveStealsBServerKey }

pred characterize_EveStealsCommServerKey {
	some t: Time {
		Key_AB in Eve.keys.t
	}
		
}  fact { !characterize_EveStealsCommServerKey }
*/

pred EventuallyAliceAndBobCommunicateWithEachOther {
	all t: Time | 
		not(Eve.nonce in Alice.knows.t) and not(Eve.nonce in Bob.knows.t)
}

assert CheckEventuallyAliceAndBobCommunicateWithEachOther { // authentication protocol
	EventuallyAliceAndBobCommunicateWithEachOther
} check CheckEventuallyAliceAndBobCommunicateWithEachOther for 12

