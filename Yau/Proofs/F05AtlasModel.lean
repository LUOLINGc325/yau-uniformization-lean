import spec.WORKPACKAGES.STATEMENTS.F05_TRANSPORT.Statements

/-! Actual chart regions and geometric consequences of the finite atlas predicate. -/

open Set
open scoped Topology ContDiff
noncomputable section

namespace Yau.Proofs.F05Aux

open Yau.Parabolic Yau.HeatConcreteBindings Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

def F05D (A : AtlasData M) (i : Fin A.count) : Set (Space n) := region (A.normal i) 2

def F05Q (A : AtlasData M) (i : Fin A.count) (T : ℝ) : Set (Point n) :=
  cylinder (F05D A i) 0 T

def F05ModelOpen (A : AtlasData M) (i : Fin A.count) : Set (Space n) :=
  match A.normal i with
  | none => univ
  | some a => {z | realCoord z a < 0}

def F05Coord (A : AtlasData M) (i : Fin A.count) (x : M.Carrier) : Space n :=
  A.forward i (chartPt (A.center i) x)

def F05Transition (A : AtlasData M) (i j : Fin A.count) : Space n → Space n :=
  fun z => F05Coord A j (lift A i z)

def F05Partition (O : Set M.Carrier) (A : AtlasData M)
    (χ : Fin A.count → M.Carrier → ℝ) : Prop :=
  (∀ i, SmoothFn (χ i)) ∧ (∀ i x, 0 ≤ χ i x) ∧
  (∀ i, tsupport (χ i) ⊆ lift A i '' Metric.closedBall 0 (1/4)) ∧
  ∃ V : Set M.Carrier, IsOpen V ∧ closure O ⊆ V ∧ ∀ x ∈ V, (∑ i, χ i x) = 1

theorem region_mono (ν : Option (RIdx n)) {r s : ℝ} (hrs : r ≤ s) :
    region ν r ⊆ region ν s := by
  intro z hz
  exact ⟨hz.1.trans hrs, hz.2⟩

theorem F05D_mem_ball {A : AtlasData M} {i : Fin A.count} {z : Space n}
    (hz : z ∈ F05D A i) : z ∈ Metric.ball 0 3 := by
  rw [Metric.mem_ball, dist_zero_right]
  exact hz.1.trans_lt (by norm_num)

theorem F05D_lift_mem_closure {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {i : Fin A.count} {z : Space n} (hz : z ∈ F05D A i) :
    lift A i z ∈ closure O := by
  obtain ⟨_, _, _, _, _, _, _, hmem⟩ := hA.1 i
  exact ((hmem z (F05D_mem_ball hz)).2.1).mpr hz.2

theorem F05D_inverse_mem_target {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {i : Fin A.count} {z : Space n} (hz : z ∈ F05D A i) :
    A.inverse i z ∈ chartTarget (A.center i) := by
  obtain ⟨_, hsub, _, _, himage, _, _, _⟩ := hA.1 i
  exact hsub (himage ⟨z, F05D_mem_ball hz, rfl⟩)

theorem F05Coord_lift {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {i : Fin A.count} {z : Space n} (hz : z ∈ F05D A i) :
    F05Coord A i (lift A i z) = z := by
  have hchart : chartPt (A.center i) (chartInv (A.center i) (A.inverse i z)) = A.inverse i z :=
    (extChartAt (ComplexModel n) (A.center i)).right_inv (F05D_inverse_mem_target hA hz)
  change A.forward i (chartPt (A.center i) (chartInv (A.center i) (A.inverse i z))) = z
  rw [hchart]
  exact (hA.1 i).2.2.2.2.2.1 z (F05D_mem_ball hz)

theorem F05_cover {O : Set M.Carrier} {A : AtlasData M} (hA : GenuineAtlas O A)
    {x : M.Carrier} (hx : x ∈ closure O) :
    ∃ i z, z ∈ F05D A i ∧ lift A i z = x := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hA.2.1 hx)
  obtain ⟨z, hz, hzx⟩ := hi
  exact ⟨i, z, region_mono (A.normal i) (by norm_num : (1 : ℝ) ≤ 2) hz, hzx⟩

end Yau.Proofs.F05Aux
