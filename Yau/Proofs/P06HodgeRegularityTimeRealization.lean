import Yau.Proofs.P06HodgeRegularityTimeFiber
import Yau.LeafProofs.L03CompletionRepresentatives

/-! The actual fibre time derivative realizes the Hilbert derivative.
Positive difference quotients and the original Fatou realization lemma
prove L² membership internally, at every positive time. -/
noncomputable section
open MeasureTheory Filter Module
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

theorem regularityRealizeL2Form_smul (g : SmoothMetric M) (μ : Measure M.Carrier)
    (a : ℝ) (u : L2FormSpace g μ k) :
    realizeL2Form g μ (a • u) = a • realizeL2Form g μ u :=
  UniformSpace.Completion.coe_smul a u

theorem regularityTimeDerivativeForm_realizes
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (h : ℝ → L2FormHilbert g μ k) (U : ℝ → RealForm M k)
    (hU : SmoothFormTime U (Set.Ioi 0))
    (hUs : ∀ s, 0 < s → ∃ hUs : L2RealForm g.form μ (U s), realizeActualForm g μ (U s) hUs = h s)
    {t : ℝ} (ht : 0 < t) {w : L2FormHilbert g μ k} (hw : HasDerivAt h w t) :
    ∃ hD : L2RealForm g.form μ (regularityTimeDerivativeForm U t),
      realizeActualForm g μ (regularityTimeDerivativeForm U t) hD = w := by
  classical
  have hpos (s : {r : ℝ // 0 < r}) := hUs s s.2
  choose hUL hreal using hpos
  let δ : ℕ → ℝ := fun m => (1/2 : ℝ)^m
  have hδpos (m : ℕ) : 0 < δ m := pow_pos (by norm_num : 0 < (1/2 : ℝ)) m
  have hδ : Tendsto δ atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num : (1/2 : ℝ) < 1)
  have hδNE : Tendsto δ atTop (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hδ,Eventually.of_forall fun m => ne_of_gt (hδpos m)⟩
  let q (m : ℕ) : L2FormSpace g μ k := (δ m)⁻¹ •
    (L2FormSpace.ofSection (U (t+δ m)) (hUL ⟨t+δ m,add_pos ht (hδpos m)⟩) -
      L2FormSpace.ofSection (U t) (hUL ⟨t,ht⟩))
  have hq (m : ℕ) : realizeL2Form g μ (q m) = (δ m)⁻¹ • (h (t+δ m) - h t) := by
    rw [regularityRealizeL2Form_smul,realizeL2Form_sub]
    change (δ m)⁻¹ • (realizeActualForm g μ (U (t+δ m)) _ - realizeActualForm g μ (U t) _) = _
    rw [hreal ⟨t+δ m,add_pos ht (hδpos m)⟩,hreal ⟨t,ht⟩]
  have hHilbert : Tendsto (fun m => realizeL2Form g μ (q m)) atTop (𝓝 w) := by
    simpa only [hq,Function.comp_def] using hw.tendsto_slope_zero.comp hδNE
  have hfiber : ∀ᵐ y ∂μ, Tendsto (fun m => (q m).toSection y) atTop
      (𝓝 (regularityTimeDerivativeForm U t y)) := by
    apply Eventually.of_forall
    intro y
    simpa only [q,L2FormSpace.toSection_smul,L2FormSpace.toSection_sub,L2FormSpace.toSection_ofSection,
      Pi.smul_apply,Pi.sub_apply,Function.comp_def] using (regularityTimeDerivativeForm_fiber_slope U hU ht y).comp hδNE
  exact realize_eq_of_ae_fiber_limit g μ q w hHilbert (regularityTimeDerivativeForm U t) hfiber

end Yau.NodeProofs.P06Aux
