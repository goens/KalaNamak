import Batteries.Data.UnionFind
import Batteries.Data.HashMap
import KalaNamak.ToBatteries
open Batteries

namespace EGraph

abbrev Id n := Fin n

structure Term (α : Type _) (n : Nat) where
  head : α
  args : Array (Id n)
deriving DecidableEq, Hashable

#eval Hashable.hash (Term.mk 1 #[0, 1, (2 : Fin 3)])

theorem Term.eq_head_args {α : Type _} {n : Nat} [DecidableEq α] {a b : Term α n} :
  a = b ↔ a.head = b.head ∧ a.args = b.args := by
  cases a; cases b
  case mk.mk head_a args_a head_b args_b =>
  simp

instance [BEq α] : BEq (Term α n) where
  beq a b := a.head == b.head && a.args == b.args

/-
theorem Term.beq_head_args {α : Type _} {n : Nat} [BEq α] {a b : Term α n} :
  a == b ↔ a.head == b.head && a.args == b.args := by
  cases a; cases b
  case mk.mk head_a args_a head_b args_b =>
  simp [BEq.beq, instBEqTerm]
-/

-- is that a good hash at all? probabbly not
instance [Hashable α] {n : Nat} : Hashable (Term α n) where
  hash a := hash a.head + hash a.args

class ToTerm (α : Type _) extends BEq α, Hashable α where
  toTerm : α → Term α n

variable (α : Type _) [ToTerm α]

-- Parents?
abbrev EClass α := Array α

end EGraph

structure EGraph (α : Type _) [BEq α] [Hashable α] where
  ufind : UnionFind
  terms : Batteries.HashMap α (EGraph.EClass α)
  classes : Batteries.HashMap (EGraph.Id ufind.size) (EGraph.EClass α)

namespace EGraph

variable {α : Type _} [BEq α] [Hashable α]

@[inherit_doc UnionFind.size, simp]
def size : EGraph α → Nat := fun e => e.ufind.size

theorem size_eq_ufind_size (e : EGraph α) : e.size = e.ufind.size := by rfl

theorem hashmap_eq_size {e : EGraph α} {n : Nat} (h : n = e.size):
  Batteries.HashMap (EGraph.Id n) (EGraph.EClass α) =
  Batteries.HashMap (EGraph.Id e.size) (EGraph.EClass α)  := by rw [h]

@[inherit_doc UnionFind.checkEquiv]
def checkEquiv (self : EGraph α) (fst snd : Fin self.size) :
  EGraph α × Bool :=
  let res := self.ufind.checkEquiv fst snd
  let hsize : res.1.size = self.size := by rw [UnionFind.size_eq_checkEquiv_size self.ufind fst snd, size_eq_ufind_size]
  let heq := hashmap_eq_size hsize
  ({self with ufind := res.1, classes := heq ▸ self.classes }, res.2)

@[inherit_doc UnionFind.checkEquiv!]
def checkEquiv! (self : EGraph α) (fst snd : Nat) :
  EGraph α × Bool :=
  if h : fst < self.size ∧ snd < self.size then
    self.checkEquiv ⟨fst, h.1⟩ ⟨snd, h.2⟩
  else
    panicWith (self, false) "index out of bounds"

@[inherit_doc UnionFind.checkEquivN]
def checkEquivN (self : EGraph α) (fst snd : Fin n) (h : n = self.size) :
  EGraph α × Bool :=
  match n, h with | _, rfl => self.checkEquiv fst snd

@[inherit_doc UnionFind.checkEquivD]
def checkEquivD (self : EGraph α) (fst snd : Nat) :
  EGraph α × Bool :=
  let sx := self.ufind.findD fst
  let sy := sx.1.findD snd
  let hsize : sy.1.size = self.ufind.size := by
    simp [sy, sx]
  ({self with ufind := sy.1, classes := hsize ▸ self.classes}, sx.2 == sy.2)

-- This should be StateM
abbrev EGraphM := StateM (EGraph α)

-- def findM : monadic version of find

def canonicalize (self : EGraph α) (t : Term α self.size) : EGraph α := Id.run do
  let mut uf := self.ufind
  for a in t.args do
    let a' = uf.find a
