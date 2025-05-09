# Memory Safety Guarantees of Generational References modeled in Forge

This project models Generational References (GR), a memory management
technique designed to ensure memory safety without the overhead of garbage
collection or the complexity of ownership systems like Rust's borrow checker.
The implementation of GR in this project is modeled is from the article [Vale's
Memory Safety Strategy: Generational References and Regions](https://verdagon.dev/blog/generational-references)
by Evan Ovadia, author of the [Vale](https://vale.dev/) programming language
which uses GR to achive memory safety. 

GR addresses critical memory safety issues like use-after-free and double-free
errors by attaching a generation counter to each memory allocation. When a
reference is created, it remembers the current generation of its allocation.
Before any dereference, the system checks if the reference's remembered
generation matches the allocation's current generation. This prevents accessing
freed or reused memory, as freeing increments the generation counter.

The goal is to formally verify that GR prevents common memory safety bugs, as
its conceptual elegance and ease of implementation, when combined with the
effectiveness it claims, seem too good to be true.

We additionally verify the safety of an optimization: when the owner of an
object is still alive, accessing that object doesn't need a GR check. Languages
that implement GR can opt-in to use single-ownership, where every object is
owned by a single struct, array, or stack frame. Under this condition, we're
guaranteed that as long as the owner is still in scope/not freed, accessing
data in the memory region that this owner owns doesn't need any checks. The most
common usage of this optimization is to remove checks for borrowed/moved
function arguments (and anything on the stack frame)
and for variables that were literally just allocated.
```cpp
void hello(Spaceship& ship) {
  // If we can verify at the call-site
  // of `hello` that `ship` is borrowed or moved, then it's definitely safe to
  // dereference `ship` without checking for safety!
  cout << ship.fuel << endl;

  Spaceship ship2;
  // Accesing the `model` field requires a dereference since `ship2` is
  // internally a pointer to a memory location on the stack frame. However, it
  // should also be obvious that it's definitely safe to access `model`.
  cout << ship2.model << endl;

  Point* pt = new Point;
  // Clearly we don't need to check if it's safe to dereference `pt` here!
  cout << pt->x << endl;

  free(pt);
  // The check should not be removed here because the owner `pt` is free-ed.
  cout << pt->x << endl;
}
```

## Model Design and Visualization

The model represents a state-based system where each `State` contains:
- A set of memory allocations
- A set of references to these allocations
- Two mappings for each allocation: its current generation and whether it's in use
- A mapping that maps every allocation to its owner.
- A set of "live" owners that are still considered "alive".

The model supports 5 key operations:
1. Creating an alias (a new, identical reference to an existing reference).
2. Allocating new memory, creating a reference to it, and attach an owner to it.
   In practice, the owner and reference are either the same thing (e.g.
   `Struct* x = new Struct`) or the owner is the stack frame and the new memory
   is for a function parameter.
3. Allocating "new" memory by reusing an unused allocation, creating a
   reference to it, and similarly attach an owner to it.
4. Creating a new owner. In practice, this is usually a new stack frame.
5. Freeing an owner and de-allocating all the allocations it owns.

Originally,
assertions were written to verify that GR prevents double-free and
use-after-free issues. However, double-free technically falls into the category
of use-after-free because one needs to "use" a reference to free itself. Hence,
proving use-after-free is enough.

As we've done multiple times in-class, this model uses linear (`is linear`)
traces to represent program execution over time. Theoretically the proofs should
still be valid, but enforcing linearity makes visualization and debugging much
easier.

In the Sterling visualizer, after time projecting over `State`, the visualizer
shows nodes that represent allocations and references, where references are
connected to the allocations that they "reference".
A `theme.json` preset is provided to ease understanding.

Unfortunately, the visualizaton can be confusing because nodes that represent
`GenerationalReference` that are created later in time can appear to be
connected. For example, the following is the initial state of a valid instance:

![State0](state0.png)

It seems that the initial state contains two references to an allocation.
However, through the Table view we find that this state actually contains **0**
references and allocations, and the shown `GenerationalReference` and
`Allocation` are both created in later states but are still displayed for
unknown reasons.

This is why the Table view became the most convenient and productive format when
debugging. Efforts to write a custom visualization was abandoned because of the
difficulty to take into account projecting over `State`.

### Why Temporal Forge Was Not Used

Temporal Forge would make many things convenient. For example, the set
`Owner` at the current time stamp would simply corresponds to all owners that
are live right now, instead of always needing to say `s.liveOwners`.

Unfortunately, we resorted to normal relational forge instead. The reason is
because of predicates like `allocateNew`:
```forge
pred allocateNew[r : GenerationalReference] {
    r.alloc not in Allocation
    r.alloc in Allocation'

    // ... other constraints
}
```

Essentially, it's impossible to get a handle to a new instance that would be
created at a future time stamp. `r.alloc not in Allocation` makes sense
time-wise but
is trivially false. Hence, if we were to use Temporal Forge, we still need
inconvenient
something like `State.allocations` which may not equal to the set of all
`Allocation`s, defeating the purpose of using Temporal Forge in the
first place.

## Signatures and Predicates

### Signatures:
- `Bool`: Simple boolean type with `True` and `False` values
- `Allocation`: Represents a memory allocation
- `GenerationalReference`: A reference with a pointer to an allocation and a
   remembered generation
- `State`: Represents system state with sets of allocations and references,
   plus mappings for generations and usage status

### Key Predicates:
- `wellformed`: Ensures the model's basic structural integrity (e.g.
  references point to valid allocations)
- `init`: Sets up a valid initial state. The main goal is to enforce the
  remembered generation of references to be lower than or equal to the current
  generation of allocations. `init` is effectively the "base case" for this
  invariant. The inductive steps are enforced by the 4 memory operation
  predicates.
- `safeReference`: The core safety check that ensures a reference's remembered
  generation matches its allocation's current generation. When a reference
  doesn't satisfy `safeReference`, this means dereferencing it might cause
  memory corruption.
- Predicates that represent our 4 memory operations:
  - `aliasReference`: Creates a duplicate reference to an existing allocation
  - `allocateNew`: Creates a new allocation and reference
  - `allocateReuse`: Reuses a freed allocation with an incremented
    generation
  - `newOwner`: Creates a new owner that doesn't own any allocations.
  - `removeOwner`: Mark an owner is not "live", marks all allocations it owns
    as unused and increments their generations.
- `nextState`: Connects states through valid operations
- `traces`: Builds valid execution sequences
- Unsafe patterns (for testing `unsat`):
  - `useAfterFree`: Attempts to use a reference after its allocation is freed
  - `useAliasAfterFree`: Attempts to use an alias after the original reference
    is freed
- Optimization failures (for testing `unsat`):
  - `liveOwnerIsNotSafe`: Claims that a reference whose allocation's owner is
    still alive is not safe to dereference.


## Testing

The model was tested through a combination of satisfiability and
unsatisfiability checks:

1. **Basic model validation**:
   - `assert traces is sat for exactly 3 State for {next is linear}`: Verifies
     that valid execution traces exist with 3 states.
   - `assert traces is sat for exactly 4 State for {next is linear}`: Extends
     validation to 4 states.
   - Various checks such as `hasGrTraceWithRemoveEmptyOwner` to make sure traces
     that use our operations actually exist and our proofs are not vacuously
     true!

2. **Safety property verification**:
   - `assert useAfterFree is unsat for {next is linear}`: Proves use-after-free
     is impossible.
   - `assert useAliasAfterFree is unsat for {next is linear}`: Proves using an
     alias after freeing is impossible.
   - `assert liveOwnerIsNotSafe is unsat for {next is linear}`: Proves that it's
     impossible that dereferencing a reference whose backing allocation is owned
     is unsafe.

These tests formally verify that the Generational References technique
successfully prevents the common memory safety issues it claims to address, and
that GR is smart enough to allows us to
skip some "dumb" and obvious checks such as for variables on the
current
stack
frame.
