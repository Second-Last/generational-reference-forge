#lang forge

open "gr.frg"

option run_sterling off

test suite for aliasReference {
	example simpleAlias is 
		{some r : GenerationalReference, s1, s2 : State | 
			aliasReference[r, s1, s2]} for {
		Bool = `T + `F
		True = `T
		False = `F
		Allocation = `A
		GenerationalReference = `R1 + `R2
		alloc = `R1 -> `A + `R2 -> `A
		State = `S1 + `S2
		next = `S1 -> `S2
		`S1.allocations = `A
		`S2.allocations = `A
		`S1.references = `R1
		`S2.references = `R1 + `R2
	}

	example notAlias is 
		{all r : GenerationalReference, s1, s2 : State | 
			not aliasReference[r, s1, s2]} for {
		Bool = `T + `F
		True = `T
		False = `F
		Allocation = `A1 + `A2
		GenerationalReference = `R1 + `R2
		alloc = `R1 -> `A1 + `R2 -> `A2
		State = `S1 + `S2
		next = `S1 -> `S2
		`S1.allocations = `A1
		`S2.allocations = `A1 + `A2
		`S1.references = `R1
		`S2.references = `R1 + `R2
	}
}

test suite for allocateNewReference {
	example simpleNew is 
		{some r : GenerationalReference, s1, s2 : State | 
			allocateNewReference[r, s1, s2]} for {
		Bool = `T + `F
		True = `T
		False = `F
		Allocation = `A
		GenerationalReference = `R1
		alloc = `R1 -> `A
		State = `S1 + `S2
		next = `S1 -> `S2
		`S2.allocations = `A
		`S2.references = `R1
	}

	example notNew is 
		{all r : GenerationalReference, s1, s2 : State | 
			not allocateNewReference[r, s1, s2]} for {
		Bool = `T + `F
		True = `T
		False = `F
		Allocation = `A1 + `A2
		GenerationalReference = `R1 + `R2
		alloc = `R1 -> `A1 + `R2 -> `A2
		State = `S1 + `S2
		next = `S1 -> `S2
		`S1.allocations = `A1
		`S2.allocations = `A1 + `A2
		`S1.references = `R1
		`S2.references = `R1 + `R2
	}
}

test suite for allocateReuseReference {
	example simpleReuse is 
		{some r : GenerationalReference, s1, s2 : State | 
			allocateReuseReference[r, s1, s2]} for {
		Bool = `T + `F
		True = `T
		False = `F
		Allocation = `A
		GenerationalReference = `R1
		alloc = `R1 -> `A
		State = `S1 + `S2
		next = `S1 -> `S2
		`S1.allocations = `A
		`S2.allocations = `A
		`S1.currentlyInUse = `A -> `F
		`S2.currentlyInUse = `A -> `T
		`S2.references = `R1

		`S1.currentGeneration = `A -> 1
		`S2.currentGeneration = `A -> 2
		`R1.rememberedGeneration = 2
	}

	example notReuse is 
		{all r : GenerationalReference, s1, s2 : State | 
			not allocateReuseReference[r, s1, s2]} for {
		Bool = `T + `F
		True = `T
		False = `F
		Allocation = `A1 + `A2
		GenerationalReference = `R1
		alloc = `R1 -> `A2
		State = `S1 + `S2
		next = `S1 -> `S2
		`S1.allocations = `A1
		`S2.allocations = `A1 + `A2
		`S1.currentlyInUse = `A1 -> `F
		`S2.currentlyInUse = `A1 -> `F + `A2 -> `T
		`S2.references = `R1

		`S1.currentGeneration = `A1 -> 1
		`S2.currentGeneration = `A1 -> 1 + `A2 -> 0
		`R1.rememberedGeneration = 0
	}
}

test suite for freeReference {
	example simpleFree is 
		{some r : GenerationalReference, s1, s2 : State | 
			freeReference[r, s1, s2]} for {
		Bool = `T + `F
		True = `T
		False = `F
		Allocation = `A
		GenerationalReference = `R1
		alloc = `R1 -> `A
		State = `S1 + `S2
		next = `S1 -> `S2
		`S1.allocations = `A
		`S2.allocations = `A
		`S1.references = `R1
		`S2.references = `R1
		`S1.currentlyInUse = `A -> `T
		`S2.currentlyInUse = `A -> `F
		`S1.currentGeneration = `A -> 1
		`S2.currentGeneration = `A -> 2
	}

	example notFree is 
		{all r : GenerationalReference, s1, s2 : State | 
			not freeReference[r, s1, s2]} for {
		Bool = `T + `F
		True = `T
		False = `F
		Allocation = `A
		GenerationalReference = `R1 + `R2
		alloc = `R1 -> `A + `R2 -> `A
		State = `S1 + `S2
		next = `S1 -> `S2
		`S1.allocations = `A
		`S2.allocations = `A
		`S1.references = `R1
		`S2.references = `R1 + `R2
	}
}
