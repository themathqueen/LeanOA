import Mathlib.Topology.ContinuousMap.ContinuousMapZero

namespace ContinuousMapZero
variable {A Y : Type*} [TopologicalSpace A] [TopologicalSpace Y]

/-- A version of `Pi.single` as an element in `C(A, Y)₀` where `single i x 0 = 0`. -/
noncomputable abbrev single [DiscreteTopology A] [DecidableEq A] [Zero Y] [Zero A] (i : A)
    (x : Y) : C(A, Y)₀ where
  toFun j := if j = 0 then 0 else (Pi.single i x : A → Y) j
  map_zero' := by simp

lemma single_def [DiscreteTopology A] [DecidableEq A] [Zero Y] [Zero A]
    (i : A) (x : Y) (j : A) :
    single i x j = if j = 0 then 0 else (Pi.single i x : A → Y) j := rfl

@[simp] lemma single_apply_of_ne_zero [DiscreteTopology A] [DecidableEq A] [Zero Y] [Zero A]
    (i : A) (x : Y) {j : A} (hj : j ≠ 0) : single i x j = (Pi.single i x : A → Y) j := by simp_all

end ContinuousMapZero
