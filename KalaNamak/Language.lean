import Batteries.Data.UnionFind
open Batteries


inductive Term
| symbol : String → Term
| application : String → List Term → Term

abbrev EClassId n := Fin n

instance {n : Nat} : Hashable (EClassId n) := inferInstanceAs (Hashable <| Fin n)
instance {n : Nat} : DecidableEq (EClassId n) := inferInstanceAs (DecidableEq <| Fin n)

inductive ENode (n : Nat)
| symbol : String → ENode n
| application : String → List (EClassId n) → ENode n

/--
An EClass is morally a set of ENodes. We model this
with a list of ENodes here, and make sure the invariants
are held separately.
-/
abbrev EClass (n : Nat) := List (ENode n)

/--
The basic data structure, an EGraph.
Defined based on Willsey et al. (POPL'21).

Since `Batteries.UnionFind` requires the index
to be `Fin n`, we parametrize the EGraph by `n`.
-/
structure EGraph (n : Nat) where
  uf : UnionFind
  ufSize : n = uf.size
  eClassMap : EClassId n → EClass n
  hashCons : ENode n → EClassId n

abbrev EGraphM n := StateM (EGraph n)

namespace EGraph

variable {n : Nat}

def lookupEClass (id : EClassId n) : EGraphM n <| EClass n := do
  let eg ← get
  let id' : Fin eg.uf.size := eg.ufSize ▸ id
  let ⟨uf', ⟨res, h⟩⟩ := eg.uf.find id'
  let _ ← set {eg with uf := uf', ufSize := h ▸ eg.ufSize}
  have hn : n = uf'.size := h ▸ eg.ufSize
  return eg.eClassMap (hn ▸ res)

end EGraph
