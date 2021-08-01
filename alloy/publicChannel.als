open util/ordering[Time]
open util/boolean

sig Time { }
abstract sig Key {}
one sig Key_AB extends Key {}

abstract sig Process {
	key: lone Key,
	message: Message lone -> Time
}

abstract sig Message {
	secret: lone Bool
}

one sig Plaintext extends Message {}
one sig Encrypted extends Message {
	key: Key_AB
}

one sig Alice extends Process {} 
one sig Bob extends Process {}
one sig Eve extends Process {}

pred init (t: Time) {
	Alice.key = Key_AB
	Bob.key = Key_AB
	Eve.key = Key_AB // attacker has access to the Key
	no Alice.message.t
	no Bob.message.t
	no Eve.message.t

}

pred AliceSendOverPlaintext (t, t': Time) {
	no Alice.message.t
	let newMsg = Alice.message.t' |
		newMsg = Plaintext and
		Eve.message.t' = newMsg and
		(newMsg.secret = True or newMsg.secret = False)
	frameProc[t,t',Bob]
}

pred AliceSendOverEncrypted (t, t': Time) {
	no Alice.message.t
	let newMsg = Alice.message.t' |
		newMsg = Encrypted and
		Eve.message.t' = newMsg and
		(newMsg.secret = True or newMsg.secret = False)
	frameProc[t,t',Bob]
}

pred BobSendOverPlaintext (t, t': Time) {
	no Bob.message.t
	let newMsg = Bob.message.t' |
		newMsg = Plaintext and
		Eve.message.t' = newMsg and
		(newMsg.secret = True or newMsg.secret = False)
	frameProc[t,t',Alice]
	
}

pred BobSendOverEncrypted(t, t': Time) {
	no Bob.message.t
	let newMsg = Bob.message.t' |
		newMsg = Encrypted and
		Eve.message.t' = newMsg and
		(newMsg.secret = True or newMsg.secret = False)
	frameProc[t,t',Alice]
}

pred AliceReceive(t, t': Time) {
	some Bob.message.t
	let msg = Bob.message.t |
		Alice.message.t' =  msg
	frameProc[t,t',Eve]
	no Bob.message.t'
}

pred BobReceive(t, t': Time) {
	some Alice.message.t
	let msg = Alice.message.t |
		Bob.message.t' =  msg
	frameProc[t,t',Eve]
	no Alice.message.t'
}

pred frameProc (t, t': Time, p: Process) {
	p.message.t = p.message.t'
}

fact Traces {
	first.init
	all t: Time - last | let t' = t.next |
		AliceSendOverPlaintext[t, t'] or
		AliceSendOverEncrypted[t, t'] or
		BobSendOverPlaintext[t, t'] or
		BobSendOverEncrypted[t, t'] or
		AliceReceive[t, t'] or
		BobReceive[t, t']
}

pred NeverSecretMessageEveCanSee {
	all t: Time | 
		some Eve.message.t implies 
		( isFalse[Eve.message.t.secret] or (Eve.message.t = Encrypted and Eve.message.t.key != Eve.key)  )
}

assert CheckNeverSecretMessageEveCanSee {
	NeverSecretMessageEveCanSee
} 

run NeverSecretMessageEveCanSee for 2

check CheckNeverSecretMessageEveCanSee for 2

pred relEqualsKey[x: Key, y: Key] {
	x = y
}

pred relKeyInKey [k1, k2: Key] {
	k1 in k2
}

pred relEqualsMessage[x: Message, y: Message] {
	x = y
}

pred relEqualsProcess[x: Process, y: Process] {
	x = y
}

pred relIsTrue[x: Bool] {
	isTrue[x]
}


/*
pred characterize_BobSendSecretEncMessageWhileEveHasKey {
	some t: Time {
		relEqualsMessage[Bob.message.t, Encrypted] &&
		isTrue[Bob.message.t.secret] &&
		relEqualsKey[Eve.key, Key_AB] &&
		relEqualsKey[Bob.key, Key_AB] &&
		relEqualsKey[Alice.key, Key_AB] 
	}	
}  fact { !characterize_BobSendSecretEncMessageWhileEveHasKey }


pred characterize_AliceSendSecretEncMessageWhileEveHasKey {
	some t: Time {
		relEqualsMessage[Alice.message.t, Encrypted] &&
		isTrue[Alice.message.t.secret] &&
		relEqualsKey[Eve.key, Key_AB] &&
		relEqualsKey[Bob.key, Key_AB] &&
		relEqualsKey[Alice.key, Key_AB]
	}
		
}  fact { !characterize_AliceSendSecretEncMessageWhileEveHasKey }

pred characterize_BobSendSecretPlainMessage {
	some t: Time {
		relEqualsMessage[Bob.message.t, Plaintext] &&
		relIsTrue[Bob.message.t.secret] &&
		relEqualsKey[Eve.key, Key_AB] &&
		relEqualsKey[Bob.key, Key_AB] &&
		relEqualsKey[Alice.key, Key_AB] 
	}
		
}  fact { !characterize_BobSendSecretPlainMessage }

pred characterize_AliceSendSecretPlainMessage {
	some t: Time {
		relEqualsMessage[Alice.message.t, Plaintext] &&
		isTrue[Alice.message.t.secret] &&
		relEqualsKey[Eve.key, Key_AB] &&
		relEqualsKey[Bob.key, Key_AB] &&
		relEqualsKey[Alice.key, Key_AB] 
	}
		
}  fact { !characterize_AliceSendSecretPlainMessage }
*/
