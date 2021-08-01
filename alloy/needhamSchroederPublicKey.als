open util/ordering[Time] as TO
sig Time { }

abstract sig Key {}
abstract sig Principal {
	knows: set Nonce -> Time,
	message: Message lone -> Time
} {}

abstract sig Nonce {}

one sig AliceNonce, BobNonce, EveNonce extends Nonce {}
one sig Server extends Principal {} 

one sig Key_PA, Key_SA, Key_PB, Key_SB, Key_PS, Key_SS, Key_PE, Key_SE extends Key {}

one sig Message {
	sender: Principal lone -> Time, 
	nonceA: Nonce lone -> Time,
       nonceB: Nonce lone -> Time,
	process: Process lone -> Time,
	key: Key lone -> Time, 
	encryption: Key lone -> Time
}

abstract sig Process extends Principal {
	server_key: one Key,
	comm_key: Key lone -> Time,
	partner: lone Process,
	nonce: one Nonce,
	keys: set Key -> Time  
} 

one sig Eve extends Process {} {
	all t: Time | comm_key.t = Key_PE 
}

one sig Alice, Bob extends Process {} {
    server_key = Key_PS
		no keys
} 


pred init (t: Time) {
	no Eve.knows.t
	no Alice.comm_key.t
	no Bob.comm_key.t
	Alice.nonce = AliceNonce
	Bob.nonce = BobNonce
	Eve.nonce = EveNonce
	Alice.knows.t = Alice.nonce
	Bob.knows.t = Bob.nonce
	Message.encryption.t = Key_SA
	Message.sender.t = Server
	Message.process.t = Alice
	no Eve.keys.t
}

pred AliceRequestBob(t, t': Time) {
	Alice.message.t.sender.t = Server
	Alice.message.t.process.t = Alice
	Alice.message.t.key.t != Key_PA
	let serverMsg = Server.message.t' | 
		(serverMsg.sender.t' = Alice and
		no serverMsg.nonceA.t' and
        	no serverMsg.nonceB.t' and
		serverMsg.process.t' = Bob and
		no serverMsg.key.t' and
		no serverMsg.encryption.t')
	noProcChange[t, t', Alice]
	noProcChange[t, t', Bob]
	Eve.keys.t' = Eve.keys.t
}

pred ServerCommWithAlice(t, t': Time) {
	Server.message.t.sender.t = Alice
	Server.message.t.process.t = Bob
	let aliceMsg = Alice.message.t' | 
		(aliceMsg.sender.t' = Server and
		no aliceMsg.nonceA.t' and
        	no aliceMsg.nonceB.t' and
		aliceMsg.process.t' = Bob and
		aliceMsg.key.t' = Key_PB and
		aliceMsg.encryption.t' = Key_SS)
	Alice.comm_key.t' = Key_PB
	Alice.knows.t' = Alice.knows.t
	noProcChange [t, t', Bob]
	Eve.keys.t' = Eve.keys.t
}

pred AliceSendToBob (t, t': Time) {
	Alice.message.t.sender.t = Server
	Alice.message.t.process.t = Bob
	let bobMsg = Bob.message.t' | 
		(bobMsg.sender.t' = Alice and
		bobMsg.nonceA.t' = Alice.nonce and
        	no bobMsg.nonceB.t' and
		bobMsg.process.t' = Alice and
		no bobMsg.key.t' and
		bobMsg.encryption.t' = Key_PB)
	Bob.comm_key.t' = Bob.message.t'.key.t'
	Bob.knows.t' = Bob.knows.t
	noProcChange[t, t', Alice]
}

// attacker intercept here
pred EveSendToBob (t, t': Time) {
	Alice.message.t.sender.t = Server
	Alice.message.t.process.t = Bob
	let bobMsg = Bob.message.t' | 
		(bobMsg.sender.t' = Eve and
		bobMsg.nonceA.t' = Alice.nonce and
        	no bobMsg.nonceB.t' and
		bobMsg.process.t' = Alice and
		no bobMsg.key.t' and
		bobMsg.encryption.t' = Key_PB)
	Bob.comm_key.t' = Bob.message.t'.key.t'
	Bob.knows.t' = Bob.knows.t
	noProcChange[t, t', Alice]
}

pred BobRequestAlice (t, t': Time)  {
	(Bob.message.t.sender.t = Alice or Bob.message.t.sender.t = Eve)
	Bob.message.t.process.t = Alice
	some Bob.message.t.nonceA.t
	let serverMsg = Server.message.t' | 
		(serverMsg.sender.t' = Bob and
		no serverMsg.nonceA.t' and
        	no serverMsg.nonceB.t' and
		serverMsg.process.t' = Alice and
		no serverMsg.key.t' and
		serverMsg.encryption.t' = Bob.server_key)
	noProcChange[t, t', Bob]
	noProcChange[t, t', Alice]
}

pred ServerCommWithBob(t, t': Time) {
	Server.message.t.sender.t = Bob
	Server.message.t.process.t = Alice
	let bobMsg = Bob.message.t' | 
		(bobMsg.sender.t' = Server and
		no bobMsg.nonceA.t' and
        	no bobMsg.nonceB.t' and
		bobMsg.process.t' = Alice and
		bobMsg.key.t' = Key_PA and
		bobMsg.encryption.t' = Key_SS)
	Bob.knows.t' = Bob.knows.t
	noProcChange [t, t', Alice]
}

pred BobSendNoncesToAlice (t, t': Time) {
	Bob.message.t.sender.t = Server
	Bob.message.t.process.t = Alice
	Bob.message.t.encryption.t = Key_SS
	Bob.comm_key.t = Key_PA
	let aliceMsg = Alice.message.t' |
		(aliceMsg.sender.t' = Bob and
		aliceMsg.nonceA.t' = Alice.nonce and
        aliceMsg.nonceB.t' = Bob.nonce and
		no aliceMsg.process.t' and
		no aliceMsg.key.t' and
		aliceMsg.encryption.t' = Key_PA)
	Alice.knows.t' = Alice.knows.t + Bob.nonce
	noProcChange[t, t', Bob]
}

pred EveSendNoncesToAlice (t, t': Time) {
	Bob.message.t.sender.t = Server
	Bob.message.t.process.t = Alice
	Bob.message.t.encryption.t = Key_SS
	Bob.comm_key.t = Key_PA
	let aliceMsg = Alice.message.t' |
		(aliceMsg.sender.t' = Eve and // attacker intercepts here
		aliceMsg.nonceA.t' = Alice.nonce and
        aliceMsg.nonceB.t' = Eve.nonce and
		no aliceMsg.process.t' and
		no aliceMsg.key.t' and
		aliceMsg.encryption.t' = Key_PA)
	Alice.knows.t' = Alice.knows.t
	noProcChange[t, t', Bob]
}

pred AliceReplyNonceToSender (t, t': Time) {
	(Alice.message.t.sender.t = Bob or Alice.message.t.sender.t = Eve)
	let bobOrEveMsg = Alice.message.t.sender.t.message.t' | 
		(bobOrEveMsg.sender.t' = Alice and
        no bobOrEveMsg.nonceA.t' and
		bobOrEveMsg.nonceB.t' = Alice.message.t.nonceB.t and
		no bobOrEveMsg.process.t' and
		no bobOrEveMsg.key.t' and
		bobOrEveMsg.encryption.t' = Alice.message.t.sender.t.comm_key.t)
	Bob.knows.t' = Bob.knows.t
	Alice.message.t.sender.t.knows.t' = Alice.message.t.sender.t.knows.t
	noProcChange[t, t', Alice]
}

pred EveSendNonceToBob (t, t': Time) {
	Eve.message.t.sender.t = Alice
	some Eve.message.t.nonceB.t
	let bobMsg = Bob.message.t' |
		(bobMsg.sender.t' = Eve and
		no bobMsg.nonceA.t' and
		bobMsg.nonceB.t' = Eve.nonce and
		no bobMsg.process.t' and
		no bobMsg.key.t' and
		bobMsg.encryption.t' = Key_PB)
	Bob.knows.t' = Eve.nonce + Bob.knows.t
	noProcChange[t, t', Alice]
}

pred StealAliceKey (t, t': Time) {
	Key_SA in Eve.keys.t
	Alice.knows.t' = Alice.knows.t + Eve.nonce
}

pred StealBobKey (t, t': Time) {
	Key_SB in Eve.keys.t
	Bob.knows.t' = Bob.knows.t + Eve.nonce
}

pred noProcChange (t, t': Time, p: Process) {
	p.comm_key.t' = p.comm_key.t
	p.knows.t' = p.knows.t
}

fact Traces {
	first.init
	all t: Time - last | let t' = t.next |
		AliceRequestBob[t, t'] 
		or ServerCommWithAlice[t, t']
		or AliceSendToBob[t, t']
		or EveSendToBob[t, t']
		or BobRequestAlice[t, t']
		or ServerCommWithBob[t, t']
        	or BobSendNoncesToAlice[t, t']
		or EveSendNoncesToAlice[t, t']
		or AliceReplyNonceToSender[t, t']
		or EveSendNonceToBob[t, t']
		or StealAliceKey[t, t']
		or StealBobKey[t, t']
		or init[t']
}

fact alwaysDifferentSender {
	all t: Time, t': t.next | Message.sender.t != Message.sender.t' 
}

fact serverDoesNotLearn {
	all t: Time, t': t.next | Server.knows.t' = Server.knows.t
}

fact diffNonces {
	Alice.nonce != Bob.nonce
	Bob.nonce != Eve.nonce
	Alice.nonce != Eve.nonce
}

fact neverForget {
	all t: Time, t': t.next, p: Principal |  #p.knows.t' >= #p.knows.t
} 

fact attackerFrame {
	all t: Time, t': t.next | no Eve.message.t implies Eve.knows.t' = Eve.knows.t 
}

fact onlyOneMessagePerPrincipal {
	all t: Time {
 		some p: Principal {
			some p.message.t && no (Principal - p).message.t
		}
	}
}

pred relHappensBefore(t: Time, t': Time) {
	t.lt[t']
}

// this predicate models the attacker forwarding a message 
// to a legitimate participant only chaning the encryption used
// on the message
/**
pred manInTheMiddle (t: Time, t': Time) {
	some p, p': Process {
		relHappensBefore[t,t']
		p.message.t.sender.t != Eve && 
		p.message.t.sender.t' = Eve &&
		p.message.t.nonceA.t = p'.message.t'.nonceA.t' &&
		p.message.t.nonceB.t = p'.message.t'.nonceB.t' &&
		p.message.t.process.t = p'.message.t'.process.t' &&
		p.message.t.key.t = p'.message.t'.key.t' &&
		p.message.t.encryption.t != p'.message.t'.encryption.t'
	}
}
*/

pred aManInTheMiddle (t: Time, t': Time) {
	t = t'.prev
	Eve.message.t.sender.t != Eve && 
	Alice.message.t.sender.t' = Eve &&
	Eve.message.t.nonceA.t = Alice.message.t'.nonceA.t' &&
	Eve.message.t.nonceB.t = Alice.message.t'.nonceB.t' &&
	Eve.message.t.process.t = Alice.message.t'.process.t' &&
	Eve.message.t.key.t = Alice.message.t'.key.t' &&
	Eve.message.t.encryption.t != Alice.message.t'.encryption.t'
}

pred bManInTheMiddle (t: Time, t': Time) {
	t = t'.prev
	Eve.message.t.sender.t != Eve && 
	Bob.message.t.sender.t' = Eve &&
	Eve.message.t.nonceA.t = Bob.message.t'.nonceA.t' &&
	Eve.message.t.nonceB.t = Bob.message.t'.nonceB.t' &&
	Eve.message.t.process.t = Bob.message.t'.process.t' &&
	Eve.message.t.key.t = Bob.message.t'.key.t' &&
	Eve.message.t.encryption.t != Bob.message.t'.encryption.t'
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



// models eve stealing alices secret, then communicating with bob 
// and having bob believe the nonce
pred characterize_EveStealsAliceSecret {
	some t: Time {
		Key_SA in Eve.keys.t 
	}
		
}  fact { !characterize_EveStealsAliceSecret }

pred characterize_EveStealsBobSecret {
	some t: Time {
		Key_SB in Eve.keys.t
	}
		
}  fact { !characterize_EveStealsBobSecret }
*/

// constrain counterexample space to only manInTheMiddle attacks
pred manInTheMiddleConstraint[t1, t2, t3, t4, t5, t6: Time] { 
	aManInTheMiddle[t1, t2] && 
	bManInTheMiddle[t3, t4] &&
	aManInTheMiddle[t5, t6]
}

pred EventuallyAliceAndBobCommunicateWithEachOther {
	all t: Time | 
		not(Eve.nonce in Alice.knows.t) and not(Eve.nonce in Bob.knows.t)
}

assert CheckEventuallyAliceAndBobCommunicateWithEachOther { 
	EventuallyAliceAndBobCommunicateWithEachOther
} check CheckEventuallyAliceAndBobCommunicateWithEachOther for 9


run EventuallyAliceAndBobCommunicateWithEachOther for 9
