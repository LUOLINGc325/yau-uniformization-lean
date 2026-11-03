import Yau.Proofs.P03ManifoldPole
import Yau.LeafProofs.L22Uniform

open scoped Manifold Topology ContDiff
open Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- Every fixed compact set avoiding the actual pole has a finite lower
bound for the global cutoff logarithm before all regularization indices. -/
theorem exists_compact_manifoldPole_lower (a : M.Carrier)
    (b : SmoothBumpFunction 𝓘(ℝ, ComplexVector n) a) (c : ℝ) (hc : 0 ≤ c)
    {K : Set M.Carrier} (hK : IsCompact K) (hKa : a ∉ K) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ j : ℕ, ∀ x ∈ K,
      -D ≤ manifoldCutoffPole c b (poleEpsilon j) x := by
  let L := K ∩ tsupport (b : M.Carrier → ℝ)
  have hL : IsCompact L := hK.inter_right (isClosed_tsupport _)
  have hsrc : L ⊆ (extChartAt (ComplexModel n) a).source :=
    fun _ hx => b.tsupport_subset_extChartAt_source hx.2
  let C := chartPt a '' L
  have hC : IsCompact C := hL.image_of_continuousOn
    ((continuousOn_extChartAt (I := ComplexModel n) a).mono hsrc)
  have hne : ∀ z ∈ C, z ≠ chartPt a a := by
    rintro z ⟨x, hx, rfl⟩ hz
    have hxa : x = a := (extChartAt (ComplexModel n) a).injOn (hsrc hx)
      (mem_extChartAt_source a) hz
    exact hKa (hxa ▸ hx.1)
  have hq : Continuous (fun z : ComplexVector n => ‖z - chartPt a a‖ ^ 2) :=
    (continuous_id.sub continuous_const).norm.pow 2
  have hlog : ContinuousOn (modelLogPole (chartPt a a) 0) C := by
    apply (hq.continuousOn.log (fun z hz =>
      ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hne z hz)))))).congr
    intro z _
    simp only [modelLogPole, add_zero]
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hlog
  let A := max B 0
  have hA : 0 ≤ A := le_max_right _ _
  refine ⟨c * A, mul_nonneg hc hA, ?_⟩
  intro j x hx
  by_cases hb : b x = 0
  · simp only [manifoldCutoffPole, hb, zero_mul, mul_zero]
    exact neg_nonpos.mpr (mul_nonneg hc hA)
  · have hxL : x ∈ L := ⟨hx, subset_closure (show x ∈ Function.support (b : M.Carrier → ℝ) from hb)⟩
    have hzC : chartPt a x ∈ C := ⟨x, hxL, rfl⟩
    have hnorm := hB (chartPt a x) hzC
    change |modelLogPole (chartPt a a) 0 (chartPt a x)| ≤ B at hnorm
    have hlower : -A ≤ modelLogPole (chartPt a a) 0 (chartPt a x) :=
      (neg_le_neg (le_max_left B 0)).trans (abs_le.mp hnorm).1
    have hqpos : 0 < ‖chartPt a x - chartPt a a‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hne _ hzC)))
    have hmono : modelLogPole (chartPt a a) 0 (chartPt a x) ≤
        modelLogPole (chartPt a a) (poleEpsilon j) (chartPt a x) := by
      simp only [modelLogPole, add_zero]
      exact Real.log_le_log hqpos (le_add_of_nonneg_right (poleEpsilon_pos j).le)
    have hp : -A ≤ b x * modelLogPole (chartPt a a) (poleEpsilon j) (chartPt a x) := by
      have hm := mul_le_mul_of_nonneg_left (hlower.trans hmono) (b.nonneg (x := x))
      have hone := b.le_one (x := x)
      nlinarith
    calc
      -(c * A) = c * (-A) := by ring
      _ ≤ c * (b x * modelLogPole (chartPt a a) (poleEpsilon j) (chartPt a x)) :=
        mul_le_mul_of_nonneg_left hp hc
      _ = manifoldCutoffPole c b (poleEpsilon j) x := rfl

end Yau.NodeProofs.P03Aux
