import Yau.Proofs.F05PhysicalTraceJets
import Yau.Proofs.F05BootstrapRestrictions

/-! Equality of actual physical values on a positive closed slab identifies
all four native jets, even when the two functions have different larger
time intervals. No exterior equality or extra derivative trace is assumed. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_physical_slab_jets_congr {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {a b T S : ℝ} (hab : a < b) (ha : 0 ≤ a)
    (hbT : b ≤ T) (hbS : b ≤ S) (u v : M.Carrier → ℝ → ℝ)
    (hu : ∀ i, C2 (F05Q A i T) (pull A i u))
    (hv : ∀ i, C2 (F05Q A i S) (pull A i v))
    (hEq : ∀ x ∈ closure O, ∀ t ∈ Icc a b, u x t = v x t) :
    ∀ i z, z ∈ cylinder (F05D A i) a b →
      spatialD (pull A i u) z = spatialD (pull A i v) z ∧
      spatialDD (pull A i u) z = spatialDD (pull A i v) z ∧
      timeD (F05Q A i T) (pull A i u) z = timeD (F05Q A i S) (pull A i v) z := by
  intro i z hz
  have hSpatial := F05_physical_trace_spatial_jets
    (F05_region_uniqueDiffOn (A.normal i) (by norm_num : (0 : ℝ) < 2))
    (pull A i u) (pull A i v) z.2
    (fun x hx => (hu i).2.2.2.2.1 (x,z.2) ⟨hx,ha.trans hz.2.1,hz.2.2.trans hbT⟩)
    (fun x hx => (hv i).2.2.2.2.1 (x,z.2) ⟨hx,ha.trans hz.2.1,hz.2.2.trans hbS⟩)
    (fun x hx => hEq (lift A i x) (F05D_lift_mem_closure hA hx) z.2 hz.2) z.1 hz.1
  have hSmallTime : timeD (cylinder (F05D A i) a b) (pull A i u) z =
      timeD (cylinder (F05D A i) a b) (pull A i v) z := by
    have hFiber : {t : ℝ | (z.1,t) ∈ cylinder (F05D A i) a b} = Icc a b := by
      ext t
      exact and_iff_right hz.1
    have hLine : EqOn (fun t => pull A i u (z.1,t)) (fun t => pull A i v (z.1,t)) (Icc a b) :=
      fun t ht => hEq (lift A i z.1) (F05D_lift_mem_closure hA hz.1) t ht
    unfold timeD
    rw [hFiber]
    exact derivWithin_congr hLine (hLine hz.2)
  have hBigTime := (F05_timeD_restrict_interval hab ha hbT (hu i) hz).symm.trans
    (hSmallTime.trans (F05_timeD_restrict_interval hab ha hbS (hv i) hz))
  exact ⟨hSpatial.1,hSpatial.2,hBigTime⟩

end Yau.Proofs.F05Aux
