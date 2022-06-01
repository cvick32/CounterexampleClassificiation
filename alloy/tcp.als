open util/ordering[Time] as TO

sig Time { }

abstract sig Message {
	sender: Process lone -> Time
}

one sig SYN, ACK, SYN_ACK, FIN, INIT extends Message {}

abstract sig Channel {
	msg: Message one -> Time
}

one sig AtoB, BtoA extends Channel {}

abstract sig ProtocolState {}

one sig ClosedState extends ProtocolState {} {}
one sig ListenState extends ProtocolState {} {}
one sig SynSentState extends ProtocolState {} {}
one sig SynRecState extends ProtocolState {} {}
one sig EstState extends ProtocolState {} {}
one sig FinW1State extends ProtocolState {} {}
one sig ClosedWaitState extends ProtocolState {} {}
one sig FinW2State extends ProtocolState {} {}
one sig ClosingState extends ProtocolState {} {}
one sig LastAckState extends ProtocolState {} {}
one sig TimeWaitState extends ProtocolState {} {}
one sig EndState extends ProtocolState {} {}
one sig AttackerState extends ProtocolState {} {}

abstract sig Process {
	state: ProtocolState one -> Time,
	readChannel: one Channel,
	writeChannel: one Channel
}

one sig Attacker extends Process {} {}

abstract sig Participant extends Process {
	read: Message lone -> Time
}
one sig TCP_A extends Participant {} {}

one sig TCP_B extends Participant {} {}

// should add this in but the traces are boring with it i// p.state.t' = EndState iff not
pred HandleClosed(t, t': Time, p: Process) {
	p.state.t = ClosedState
	p.read.t = p.read.t'
	((p.state.t' = ListenState and
	  noChannelChange[t, t'])
 	 iff not
	 (p.state.t' = SynSentState and
	  p.writeChannel.msg.t' = SYN and
	  p.writeChannel.msg.t'.sender.t' = p and
	  thisChannelNoChange[t, t', p.readChannel]))
}

pred HandleListen(t, t': Time, p: Process) {
	p.state.t = ListenState
	((p.readChannel.msg.t = SYN and
	  p.read.t' = SYN and
	  p.read.t'.sender.t' = SYN.sender.t and
	  p.state.t' = SynRecState and
	  p.writeChannel.msg.t' = SYN_ACK and
	  p.writeChannel.msg.t'.sender.t' = p and
	  thisChannelNoChange[t, t', p.readChannel])
	 iff not
	 (p.state.t' = ClosedState and
	  noChannelChange[t, t'] and
	  p.read.t = p.read.t'))
}

pred HandleSynSent(t, t': Time, p: Process) {
	p.state.t = SynSentState
	((p.readChannel.msg.t = SYN and
	  p.read.t' = SYN and
	  p.read.t'.sender.t' = SYN.sender.t and
	  p.state.t' = SynRecState and
	  p.writeChannel.msg.t' = SYN_ACK and
	  p.writeChannel.msg.t'.sender.t' = p and
	  thisChannelNoChange[t, t', p.readChannel])
	 iff not
	 (p.readChannel.msg.t = SYN_ACK and
	  p.read.t' = SYN_ACK and
	  p.read.t'.sender.t' = SYN_ACK.sender.t and
	  p.state.t' = EstState and
	  p.writeChannel.msg.t' = SYN_ACK and
	  p.writeChannel.msg.t'.sender.t' = p and
	  thisChannelNoChange[t, t', p.readChannel])
	 iff not
	 (p.state.t' = ClosedState and
	  noChannelChange[t, t'] and
	  p.read.t = p.read.t'))
}

pred HandleSynRec(t, t': Time, p: Process) {
	p.state.t = SynRecState
	noChannelChange[t, t']
	((p.readChannel.msg.t = SYN_ACK and
	  p.read.t' = SYN_ACK and
	  p.read.t'.sender.t' = SYN_ACK.sender.t and
	  p.state.t' = EstState))
}

pred HandleEstablished(t, t': Time, p: Process) {
	p.state.t = EstState
	((p.writeChannel.msg.t' = FIN and
	  p.writeChannel.msg.t'.sender.t' = p and
	  p.state.t' = FinW1State and
	  p.read.t = p.read.t' and
	  thisChannelNoChange[t, t', p.readChannel])
 	 iff not
	 (p.readChannel.msg.t = FIN and
	  p.read.t' = FIN and
	  p.read.t'.sender.t' = FIN.sender.t and
 	  p.state.t' = ClosedWaitState and
	  p.writeChannel.msg.t' = ACK and
	  p.writeChannel.msg.t'.sender.t' = p and
	  thisChannelNoChange[t, t', p.readChannel]))
}
pred HandleFinWait1(t, t': Time, p: Process) {
	p.state.t = FinW1State
	((p.readChannel.msg.t = FIN and
	  p.read.t' = FIN and
	  p.read.t'.sender.t' = FIN.sender.t and
	  p.state.t' = ClosingState and
 	  p.writeChannel.msg.t' = ACK and
	  p.writeChannel.msg.t'.sender.t' = p and
	  thisChannelNoChange[t, t', p.readChannel])
 	 iff not
	 (p.readChannel.msg.t = ACK and
	  p.read.t' = ACK and
	  p.read.t'.sender.t' = ACK.sender.t and
	  p.state.t' = FinW2State and
 	  noChannelChange[t, t']))
}

pred HandleClosedWait(t, t': Time, p: Process) {
	p.state.t = ClosedWaitState
	p.read.t = p.read.t'
	((p.writeChannel.msg.t' = FIN and
	  p.writeChannel.msg.t'.sender.t' = p and
	  p.state.t' = LastAckState and
	  thisChannelNoChange[t, t', p.readChannel]))
}

pred HandleFinWait2(t, t': Time, p: Process) {
	p.state.t = FinW2State
	((p.readChannel.msg.t = FIN and
	  p.read.t' = FIN and
	  p.read.t'.sender.t' = FIN.sender.t and
	  thisChannelNoChange[t, t', p.readChannel] and
	  p.state.t' = TimeWaitState and
	  p.writeChannel.msg.t'.sender.t' = p and
	  p.writeChannel.msg.t' = ACK))
}

pred HandleClosing(t, t': Time, p: Process) {
	p.state.t = ClosingState
	noChannelChange[t, t']
	((p.readChannel.msg.t = ACK and
	  p.read.t' = ACK and
	  p.read.t'.sender.t' = ACK.sender.t and
	  p.state.t' = TimeWaitState))
}

pred HandleLastAck(t, t': Time, p: Process) {
	p.state.t = LastAckState
	noChannelChange[t, t']
	((p.readChannel.msg.t = ACK and
	  p.read.t' = ACK and
	  p.read.t'.sender.t' = ACK.sender.t and
	  p.state.t' = ClosedState))
}

pred HandleTimeWait(t, t': Time, p: Process) {
	p.state.t = TimeWaitState
	p.state.t' = ClosedState
	noChannelChange[t, t']
}

pred HandleEndState(t, t': Time, p: Process) {
	p.state.t = EndState
	noChannelChange[t, t']
}

pred AttackerModel(t, t': Time) {
	noProcChange[t,t',TCP_A] and
	noProcChange[t,t',TCP_B] and
	one c: Channel, m: Message | c.msg.t' = m and
						     c.msg.t'.sender.t' = Attacker and
  						     m != INIT and
						     thisChannelNoChange[t, t', Channel - c]
}

pred init (t: Time) {
	TCP_A.state.t = ClosedState and
	TCP_B.state.t = ClosedState and
	TCP_A.readChannel = BtoA and
	TCP_A.writeChannel = AtoB and
	TCP_B.readChannel= AtoB and
	TCP_B.writeChannel = BtoA and
	AtoB.msg.t = INIT and
	BtoA.msg.t = INIT and
	no AtoB.msg.t.sender.t and
	no BtoA.msg.t.sender.t and
	no TCP_A.read.t and
	no TCP_B.read.t
}

fact Traces {
	init[first] and
	all t: Time - last | let t' = t.next |
	(AttackerModel[t, t']) iff not
	(one p: Participant |
		noProcChange[t, t', Participant - p] and
	(HandleClosed[t, t', p]
	 iff not HandleListen[t, t', p]
	 iff not HandleSynSent[t, t', p]
	 iff not HandleSynRec[t, t', p]
	 iff not HandleEstablished[t, t', p]
	 iff not HandleFinWait1[t, t', p]
	 iff not HandleClosedWait[t, t', p]
	 iff not HandleFinWait2[t, t', p]
	 iff not HandleClosing[t, t', p]
	 iff not HandleLastAck[t, t', p]
	 iff not HandleEndState[t, t', p]))
}

fact {
	all t: Time | Attacker.state.t = AttackerState
}

// or !(some p: Participant | p.read.t = m))
fact {
	all m: Message, t:Time | !(some c: Channel | c.msg.t = m)  implies no m.sender.t
}

fact {
	all t: Time | TCP_A.state.t != AttackerState and TCP_B.state.t != AttackerState
}


pred thisChannelNoChange(t, t': Time, c: Channel) {
	c.msg.t = c.msg.t' and
	c.msg.t.sender.t = c.msg.t'.sender.t'
}

pred noChannelChange(t, t': Time) {
	AtoB.msg.t = AtoB.msg.t' and
	AtoB.msg.t.sender.t = AtoB.msg.t'.sender.t' and
	BtoA.msg.t = BtoA.msg.t' and
	BtoA.msg.t.sender.t = BtoA.msg.t'.sender.t'
}

pred noProcChange(t, t': Time, p: Participant) {
	p.state.t = p.state.t' and
	p.read.t = p.read.t'
}

pred LeadsTo(s1, s2: ProtocolState) {}

// phi 1
pred NoHalfClosedConnectionEst {
	all t: Time |
		(TCP_A.state.t = ClosedState) implies !(TCP_B.state.t = EstState)
}

//check NoHalfClosedConnectionEst for 10

run NoHalfClosedConnectionEst for 10

assert CheckNoHalfClosedConnectionEst {
	NoHalfClosedConnectionEst
} check CheckNoHalfClosedConnectionEst for 7



// phi 3
pred PeersDoNotGetStuck {
	!(some t: Time | all t': t.nexts |
	  TCP_A.state.t' = TCP_A.state.t and
 	  TCP_B.state.t' = TCP_B.state.t and
	  TCP_A.state.t != EndState and
	  TCP_B.state.t != EndState)
}

assert CheckPeersDoNotGetStuck {
		PeersDoNotGetStuck
} check CheckPeersDoNotGetStuck for 10



pred test { some t: Time | TCP_A.state.t = SynSentState}
run test for 10


// Classification Predicates
pred relEqualsMessage(x, y: Message) {
	x = y
}

pred relAInState(s: ProtocolState, t:Time) {
	TCP_A.state.t = s
}

pred relBInState(s: ProtocolState, t:Time) {
	TCP_B.state.t = s
}

pred relEqualsProcess(x, y: Participant) {
	x = y
}

pred msgSameSender(m,m': Message, t: Time) {
	m.sender.t = m'.sender.t
}

pred attackerSentMsg(m: Message, t: Time) {
	m.sender.t = Attacker
}

pred relNotEqualsTime(x: Time, y: Time) {
	!(x = y)
}

pred relHappensBefore (t: Time, t': Time) {
	t.lt[t']
}

pred msgInAChannel(m: Message, t: Time) {
	AtoB.msg.t = m
}

pred msgInBChannel(m: Message, t: Time) {
	BtoA.msg.t = m
}

pred AReadAttacker(t: Time) {
	TCP_A.read.t.sender.t = Attacker
}

pred BReadAttacker(t: Time) {
	TCP_B.read.t.sender.t = Attacker
}


pred attackerSentSyn(t: Time) {
	SYN.sender.t = Attacker
}

pred attackerSentSynAck(t: Time) {
	SYN_ACK.sender.t = Attacker
}
