#lang forge/froglet

option run_sterling off

abstract sig Player {}
one sig PlayerA, PlayerB extends Player {}

sig State {
	pile: one Int,
	player: lone Player,
	next: lone State
}

pred wellformed {
	all s : State | {
		0 <= s.pile
	}
}

pred move[k : Int, s1 : State, s2 : State] {
	s1.player != s2.player
	s1.pile > s2.pile
	subtract[s1.pile, s2.pile] <= k
}

pred trace[k : Int] {
	wellformed

	// every next is a valid move
	all s : State | some s.next implies {
		move[k, s, s.next]
	}

	some firstState : State | some lastState : State | {
		// firstState is the head
		no s : State | s.next = firstState
		// lastState is the tail
		no lastState.next
		// the game ends when all sticks are removed
		lastState.pile = 0
	}
}

pred wins[k : Int, winner : Player] {
	trace[k]

	all lastState : State | no lastState.next implies {
		winner != lastState.player
	}
}

test expect {
	possibleWith1State: {trace[5]} for exactly 1 State for {next is linear} is sat
	possibleWith2State: {trace[5]} for exactly 2 State for {next is linear} is sat
	possibleWith3State: {trace[5]} for exactly 3 State for {next is linear} is sat
	possibleWith4State: {trace[5]} for exactly 4 State for {next is linear} is sat
	possibleWith5State: {trace[5]} for exactly 5 State for {next is linear} is sat
}

// sig TIME {
// 	b: one Board,
// 	p: one Player,
// 	next: lone TIME
// }
//
// pred wellformed {
// 	all b : Board, i : Int | (i < 0 or i > 1) implies {
// 		no b.stacks[i]
// 	} else {
// 		b.stacks[i] >= 0
// 	}
// }
//
// pred move[b1 : Board, b2 : Board] {
// 	some i : Int | all j : Int | i = j implies {
// 		b1.stacks[i] > b2.stacks[i]
// 	} else {
// 		b1.stacks[j] = b2.stacks[j]
// 	}
// }
//
// pred nextTime[t1, t2 : TIME] {
// 	move[t1.b, t2.b]
// 	t1.p != t2.p
// }
//
// pred traces {
// 	wellformed
//
// 	some firstState : TIME | some lastState : TIME | {
// 		no t : TIME | t.next = firstState
// 		no lastState.next
// 		all t : TIME | t != lastState implies {
// 			nextTime[t, t.next]
// 		}
// 	}
// }
//
// example traceWith5times is {
// 	traces
// } for {
// 	Player = `A + `B
// 	PlayerA = `A
// 	PlayerB = `B
// 	Board = `B0 + `B1 + `B2 + `B3 + `B4
// 	TIME = `T0 + `T1 + `T2 + `T3 + `T4
// 	b = `T0 -> `B0 + `T1 -> `B1 + `T2 -> `B2 + `T3 -> `B3 + `T4 -> `B4
// 	p = `T0 -> `A + `T1 -> `B + `T2 -> `A + `T3 -> `B + `T4 -> `A
// 	next = `T0 -> `T1 + `T1 -> `T2 + `T2 -> `T3 + `T3 -> `T4
// 	stacks = `B0 -> 0 -> 5 + `B1 -> 0 -> 4 + `B2 -> 0 -> 3 + `B3 -> 0 -> 2 
// 			 + `B4 -> 0 -> 1
// }
//
// test expect {
// 	possibleWith4Times: {traces} for exactly 4 TIME for {next is linear} is sat
//
// 	possibleWith5Times: {traces} for 5 TIME for {next is linear} is sat
// }

// run {
// 	traces
// } for exactly 5 TIME -- for {next is linear}
