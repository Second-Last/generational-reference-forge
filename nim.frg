#lang forge/froglet

option run_sterling off

sig Board {
	stacks: pfunc Int -> Int
}

abstract sig Player {}
one sig PlayerA, PlayerB extends Player {}

sig TIME {
	b: one Board,
	p: one Player,
	next: lone TIME
}

pred wellformed {
	all b : Board, i : Int | (i < 0 or i > 1) implies {
		no b.stacks[i]
	} else {
		b.stacks[i] >= 0
	}
}

pred move[b1 : Board, b2 : Board] {
	some i : Int | all j : Int | i = j implies {
		b1.stacks[i] > b2.stacks[i]
	} else {
		b1.stacks[j] = b2.stacks[j]
	}
}

pred nextTime[t1, t2 : TIME] {
	move[t1.b, t2.b]
	t1.p != t2.p
}

pred traces {
	wellformed

	some firstState : TIME | some lastState : TIME | {
		no t : TIME | t.next = firstState
		no lastState.next
		all t : TIME | t != lastState implies {
			nextTime[t, t.next]
		}
	}
}

example traceWith5times is {
	traces
} for {
	Player = `A + `B
	PlayerA = `A
	PlayerB = `B
	Board = `B0 + `B1 + `B2 + `B3 + `B4
	TIME = `T0 + `T1 + `T2 + `T3 + `T4
	b = `T0 -> `B0 + `T1 -> `B1 + `T2 -> `B2 + `T3 -> `B3 + `T4 -> `B4
	p = `T0 -> `A + `T1 -> `B + `T2 -> `A + `T3 -> `B + `T4 -> `A
	next = `T0 -> `T1 + `T1 -> `T2 + `T2 -> `T3 + `T3 -> `T4
	stacks = `B0 -> 0 -> 5 + `B1 -> 0 -> 4 + `B2 -> 0 -> 3 + `B3 -> 0 -> 2 
			 + `B4 -> 0 -> 1
}

test expect {
	possibleWith4Times: {traces} for exactly 4 TIME for {next is linear} is sat

	possibleWith5Times: {traces} for 5 TIME for {next is linear} is sat
}

// run {
// 	traces
// } for exactly 5 TIME -- for {next is linear}
