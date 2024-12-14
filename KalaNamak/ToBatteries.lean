import Batteries.Data.UnionFind

open Batteries
namespace UnionFind

theorem size_eq_checkEquiv_size (uf : UnionFind) (x y : Fin uf.size)
 : (uf.checkEquiv x y).1.size = uf.size := by
  simp [UnionFind.checkEquiv]

theorem size_eq_checkEquiv!_size (uf : UnionFind) (x y : Nat)
 : (uf.checkEquiv! x y).1.size = uf.size := by
  unfold UnionFind.checkEquiv!
  split <;> simp [UnionFind.checkEquiv!]
  apply size_eq_checkEquiv_size

@[simp] theorem findD_size (self : UnionFind) (x : Nat) :
    (self.findD x).1.size = self.size := by
      simp [UnionFind.findD]
      split
      · case isTrue _ =>
          apply UnionFind.find_size
      · case isFalse _ =>
          simp

theorem size_eq_checkEquivD_size (uf : UnionFind) (x y : Nat)
 : (uf.checkEquivD x y).1.size = uf.size := by
   simp [UnionFind.checkEquivD]
