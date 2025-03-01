#lang forge

abstract Bool {}
one sig True, False extends Bool {}

sig Allocation {
	// currentlyInUse: lone Bool
	// currentGeneration: one Int
}

sig GenerationalReference {
	alloc: one Allocation,
	rememberedGeneration: one Int
}

sig State {
	allocations: set Allocation,
	references: set GenerationalReference,
	currentGeneration: pfunc Allocation -> Int,
	currentlyInUse: pfunc Allocation -> Bool,
	next: lone State
}

pred wellformed {
	all s : State | {
		all ref : s.references | {
			// can't reference unknown memory (allocations)
			ref.alloc in s.allocations
			// generation starts at 0
			ref.rememberedGeneration >= 0
		}

		all a : Allocation | {
			// `currentGeneration` and `currentlyInUse` only tracks allocations
			// that belong to the current state.
			a in s.allocations <=> some s.currentGeneration[a]
			a in s.allocations <=> some s.currentlyInUse[a]
			// generation starts at 0
			a in s.allocations => s.currentGeneration[a] >= 0
		}
	}
}

pred reAllocate[a : Allocation, s1, s2 : State] {
	// the allocation must exist already
	a in s1.allocations
	s1.allocations = s2.allocations
	// alloc should not be in use in s1
	s1.currentlyInUse[a] = False
	// alloc in use in s2
	s2.currentlyInUse[a] = True
	// generation increase by 1
	s2.currentGeneration[a] = add[s1.currentGeneration[a], 1]
}

pred freeAlloc[a : Allocation, s1, s2 : State] {
	// the allocation must exist already
	a in s1.allocations
	a in s2.allocations
	// alloc should be in use in s1
	s1.currentlyInUse[a] = True
	some s1.currentGeneration[a]
	// alloc should NOT be in use in s2
	s2.currentlyInUse[a] = False
	some s2.currentGeneration[a]
}

pred newAllocate[a : Allocation, s1, s2 : State] {
	// a doesn't exist in s1
	not a in s1.allocations
	no s1.currentlyInUse[a]
	no s1.currentGeneration[a]
	// a exists in s2
	a in s2.allocations
	s2.currentlyInUse[a] = True
	s2.currentGeneration[a] = 1
}

pred transition[s1, s2 : State] {
	// allocations may be freed but are never removed
	all a : s1.allocations | a in s2.allocations
	// We can perfrom one of the three operations:
	// freeAllocate, newAllocate, or reAllocate
	some a : Allocation | {
		freeAllocate[a, s1, s2]
		or newAllocate[a, s1, s2]
		or reAllocate[a, s1, s2]
	}
}

pred safeReference[r : GenerationalReference, s : State] {
	// TODO: prove that this is unnecessary
	// s.currentlyInUse[r.alloc] = True
	r.rememberedGeneration = s.currentGeneration[r.alloc]
	// TODO: prove that rememberedGeneration is <= currentGeneration
}

one sig StateA, StateB, StateC extends State {}
