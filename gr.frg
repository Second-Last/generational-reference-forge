#lang forge

option run_sterling on

abstract sig Bool {}
one sig True, False extends Bool {}

sig Owner {}

sig Allocation {}

sig GenerationalReference {
	alloc: one Allocation,
	rememberedGeneration: one Int
}

sig State {
	allocations: set Allocation,
	references: set GenerationalReference,
	currentGeneration: pfunc Allocation -> Int,
	currentlyInUse: pfunc Allocation -> Bool,
	next: lone State,

	ownedBy: pfunc Allocation -> Owner,
	liveOwners: set Owner
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

		// Owner requirement:
		// any allocation that's currently in use must have a live owner.
		all a : Allocation | (s.currentlyInUse[a] = True) => {
			some o: Owner | (s.ownedBy[a] = o and o in s.liveOwners)
		}
		// A owner can own nothing (e.g. the start of a stack frame)
		all o : Owner | some ~(s.ownedBy)[o] => o in s.liveOwners
	}

	// Owner cannot be reuse once removed
	all o : Owner
		| all disj s1, s2, s3 : State
		| (reachable[s2, s1, next] and reachable[s3, s2, next]) => {
		(o in s1.liveOwners and o not in s2.liveOwners) => o not in s3.liveOwners
	}

	// Remove clutter:
	// so we don't have "dangling" references and allocations that don't belong
	// to any state
	all ref : GenerationalReference | some s : State {
		ref in s.references
	}
	all a : Allocation | some s : State {
		a in s.allocations
	}
}

pred init[s : State] {
	all r : s.references | {
		let a = r.alloc | {
			// // can't reference unknown memory (allocations)
			// a in s.allocations
			// TODO: prove that rememberedGeneration is <= currentGeneration for
			// all subsequent states
			r.rememberedGeneration <= s.currentGeneration[a]
		}
	}
}

// In an implementation of GR, a `safeReference` check is performed before any
// dereferencing of a pointer/reference (including `free`). Then,
// if `safeReference` is violated, we raise a run-time error to prevent
// accessing prohibited data (hence ensuring memory "safety").
pred safeReference[r : GenerationalReference, s : State] {
	r.rememberedGeneration = s.currentGeneration[r.alloc]
}

// There are five operations we can perform:
// 1. A new, identical reference is created from an existing reference.
// 2. A new reference is created by allocating a new allocation. The new
//    allocation is attached to a may or may not new but live owner.
// 3. A new reference is created by allocating from an existing, unused
//    allocation. The allocation is attached to a may or may not new but 
//    live owner.
// 4. An owner is created that owns no allocations. In practice, this owner is
//    usually a stack frame and this happens when that stack frame was just
//    created.
// 5. A owner is removed, freeing all allocations it owns. In practice, the
//    owner is usually a stack frame or an owning reference to an object on the
//    heap.

pred aliasReference[r : GenerationalReference, s1, s2 : State] {
	// new reference
	not r in s1.references
	// the new reference is the only change we have
	s1.references + r = s2.references
	s1.allocations = s2.allocations
	s1.currentlyInUse = s2.currentlyInUse
	s1.currentGeneration = s2.currentGeneration
	s1.ownedBy = s2.ownedBy
	s1.liveOwners = s2.liveOwners

	// `r1` is essentially the alias of an existing reference `r2`.
	some r2 : s1.references | {
		r2.alloc = r.alloc
		r2.rememberedGeneration = r.rememberedGeneration
	}
}

pred allocateNew[r : GenerationalReference, o : Owner, s1, s2 : State] {
	let a = r.alloc | {
		// set initial generation
		r.rememberedGeneration = 0

		// new reference
		not r in s1.references
		s1.references + r = s2.references
		// new allocation
		s1.allocations + a = s2.allocations

		// `a` doens't exist in s1
		not a in s1.allocations
		no s1.currentlyInUse[a]
		no s1.currentGeneration[a]
		// `a` exists in `s2`
		a in s2.allocations
		s2.currentlyInUse[a] = True
		s2.currentGeneration[a] = 0

		// a live owner is assigned to `a`
		s2.ownedBy[a] = o
		s1.liveOwners + o = s2.liveOwners

		// currentlyInuse and currentGeneration remains the same except for `a`
		all a2 : Allocation | a != a2 => {
			s1.currentlyInUse[a2] = s2.currentlyInUse[a2]
			s1.currentGeneration[a2] = s2.currentGeneration[a2]
			s1.ownedBy[a2] = s2.ownedBy[a2]
		}
	}
}

pred allocateReuse[r : GenerationalReference, o : Owner, s1, s2 : State] {
	let a = r.alloc | {
		// set initial generation
		r.rememberedGeneration = s2.currentGeneration[a]

		// new reference
		not r in s1.references
		s1.references + r = s2.references
		// existing allocation
		a in s1.allocations
		s1.allocations = s2.allocations

		// a live owner is assigned to `a`
		s2.ownedBy[a] = o
		s1.liveOwners + o = s2.liveOwners

		// `a` should be unused in `s1`
		s1.currentlyInUse[a] = False
		// update `a` in s2
		s2.currentlyInUse[a] = True
		s2.currentGeneration[a] = add[s1.currentGeneration[a], 1]

		// `currentlyInuse` and `currentGeneration` remains the same except for `a`
		all a2 : Allocation | a != a2 => {
			s1.currentlyInUse[a2] = s2.currentlyInUse[a2]
			s1.currentGeneration[a2] = s2.currentGeneration[a2]
			s1.ownedBy[a2] = s2.ownedBy[a2]
		}
	}
}

// Only adds a new `Owner` (e.g. a new stack frame), nothing else changes.
pred newOwner[o : Owner, s1, s2 : State] {
	// Owner must be new
	o not in s1.liveOwners
	o in s2.liveOwners

	s1.allocations = s2.allocations
	s1.references = s2.references
	s1.currentGeneration = s2.currentGeneration
	s1.currentlyInUse = s2.currentlyInUse
	s1.ownedBy = s2.ownedBy
}

// A owner is removed.
// e.g. a pointer that owns some variable(s)
// or a stack frame is popped.
pred removeOwner[o : Owner, s1, s2 : State] {
	o in s1.liveOwners
	o not in s2.liveOwners

	let ownedAllocs = ~(s1.ownedBy)[o] | no ownedAllocs => {
		s1.allocations = s2.allocations
		s1.references = s2.references
		s1.currentGeneration = s2.currentGeneration
		s1.currentlyInUse = s2.currentlyInUse
		s1.ownedBy = s2.ownedBy
	} else {
		// s1.allocations - ownedAllocs = s2.allocations
		// s1.allocations = s2.allocations + ownedAllocs
		// allocations are freed but are never deleted:
		s1.allocations = s2.allocations
		s1.references = s2.references

		all a : s1.allocations | a in ownedAllocs => {
			// we also increments generation after freeing
			s2.currentGeneration[a] = add[s1.currentGeneration[a], 1]
			// `a` should be used in `s1`
			s1.currentlyInUse[a] = True
			// `a` should not be used in `s2`
			s2.currentlyInUse[a] = False
		} else {
			s1.currentGeneration[a] = s2.currentGeneration[a]
			s1.currentlyInUse[a] = s2.currentlyInUse[a]
			s1.ownedBy[a] = s2.ownedBy[a]
		}
	}
}

pred nextState[s1, s2 : State] {
	(some r : GenerationalReference | {
		aliasReference[r, s1, s2]
	}) or
	(some o : Owner | {
		newOwner[o, s1, s2] or
		removeOwner[o, s1, s2]
	}) or
	(some r : GenerationalReference, o : Owner | {
		allocateNew[r, o, s1, s2] or
		allocateReuse[r, o, s1, s2]
	})
}

pred traces {
	wellformed

	some firstState : State | some lastState : State | {
		init[firstState]
		no s : State | s.next = firstState
		no lastState.next
		all s : State | s != lastState => nextState[s, s.next]
	}
}

// Ensure that there are actually traces that exist!
hasGrTraceWithLen3: assert traces is sat for exactly 3 State for {next is linear}
hasGrTraceWithLen4: assert traces is sat for exactly 4 State for {next is linear}

// Make sure we can add an empty owner by e.g. new stack frame
hasGrTraceWithNewEmptyOwner: assert {
	traces
	some s : State, o : Owner | newOwner[o, s, s.next]
} is sat for 4 State for {next is linear}

// Make sure we can add an owner and remove it immediately
hasGrTraceWithRemoveEmptyOwner: assert {
	traces
	some s : State, o : Owner | {
		newOwner[o, s, s.next]
		removeOwner[o, s.next, s.next.next]
	}
} is sat for 4 State for {next is linear}

// Make sure an empty owner can own a new allocation (e.g. a stack variable)
hasGrTraceWithEmptyOwnerOwnsAlloc: assert {
	traces
	some s : State, o : Owner, r : GenerationalReference {
		newOwner[o, s, s.next]
		allocateNew[r, o, s.next, s.next.next]
	}
} is sat for 3 State for {next is linear}

// Make sure we can remove a owner that owns some allocation(s)
hasGrTraceWithAllocAndRemove: assert {
	traces
	#GenerationalReference = 1
	#Owner = 1
	#Allocation = 1
	some s : State, r : GenerationalReference, o : Owner | {
		allocateNew[r, o, s, s.next]
		removeOwner[o, s.next, s.next.next]
	}
} is sat for exactly 3 State for {next is linear}

// Make sure we can reuse allocation and then free it by removing its owner
hasGrTraceWithAllocReuseAndRemove: assert {
	traces
	#GenerationalReference = 2
	#Owner = 2
	#Allocation = 1
	some s : State, r1, r2 : GenerationalReference, o1, o2 : Owner | {
		allocateNew[r1, o1, s, s.next]
		removeOwner[o1, s.next, s.next.next]
		allocateReuse[r2, o2, s.next.next, s.next.next.next]
		removeOwner[o2, s.next.next.next, s.next.next.next.next]
	}
} is sat for exactly 5 State for {next is linear}


// Two common memory-safety issues: double-free and use-after-free.
// Double-free is a subset of use-after-free because by "freeing" a
// reference/allocation you're also using that reference/allocation to free it.
// Therefore, `doubleFree` is not needed and can be replaced by `useAfterFree`.

pred useAfterFree {
	traces

	some s1, s2 : State, o : Owner, r : GenerationalReference | {
		reachable[s2, s1, next]

		// `r` is some reference owned by `o`
		s1.ownedBy[r.alloc] = o
		// `o` is dropped, so all allocations it owns must be freed
		removeOwner[o, s1, s2]
		// now try to reference `r` again
		safeReference[r, s2]
	}
}

pred useAliasAfterFree {
	traces

	some disj s1, s2 : State, o : Owner, r1, r2 : GenerationalReference | {
		reachable[s2, s1, next]

		// `r2` is an alias of `r1`
		r1.alloc = r2.alloc
		r1.rememberedGeneration = r2.rememberedGeneration

		// `r1`/`r2`'s allocation are owned by `o`
		s1.ownedBy[r1.alloc] = o
		// `o` is dropped, so all allocations it owns must be freed
		removeOwner[o, s1, s2]
		// now try to reference `r2` again
		safeReference[r2, s2]
	}
}

// Dereferencing a reference after it's freed is a run-time error
noUseAfterFreeInGr: assert useAfterFree is unsat for {next is linear}
// After we free a reference, dereferencing any of its aliases is also a run-time
// error
noUseAliasAfterFreeInGr: assert useAliasAfterFree is unsat for {next is linear}

// Now let's prove that single ownership allows us to skip generation checks.

// If the owner of a reference's allocation is still "(a)live", then we can
// de-reference the reference without the check.
//
// Judging from the code, it may seem like at runtime we need to find the owner
// of the reference. In practice, the owner of any reference is track-able by
// using a borrow checker or a single-ownership model. For example, the most
// common use case
// of this optimization is to skip checks when you access a field of an object
// you just created:
// ```cpp
// int main() {
//   Point* pt = new Point;
//   std::cout << pt->x << std::endl; // clearly `pt` is safe to dereference
// }
// ```
//
// It should be obvious that in this case, we can track ownership
// rather trivially at compile-time.
pred liveOwnerIsNotSafe {
	traces

	some s0, s : State, r : GenerationalReference, o : Owner | {
		reachable[s, s0, next]

		// This makes sure we're getting the owner to the reference.
		// In the implementation, the programming language's semantic allows the
		// owner to be tracked so the implementation doesn't need to do this
		// sort of "time travel" at run-time to get the owner of the reference.
		some r0 : GenerationalReference | {
			// Handle the case that `r` is an alias.
			r.alloc = r0.alloc
			r.rememberedGeneration = r0.rememberedGeneration

			(allocateNew[r0, o, s0, s0.next] or allocateReuse[r0, o, s0, s0.next])
		}

		// the reference's allocation is currently owned by a live owner.
		// In practice, this usually means we're accessing a field directly
		// from a pointer that owns the object. In other words, `r` is `o` in
		// the programming language.
		o in s.liveOwners

		// however, the reference is not safe to access!
		not safeReference[r, s]
	}
}

liveOwnerAlwaysSafe: assert liveOwnerIsNotSafe is unsat for {next is linear}
