import Yau.Proofs.P03HilbertWeightMultiplier

open scoped Manifold Topology ContDiff ENNReal
open Set Filter MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar Yau.LeafProofs.L14Aux

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (Bundle.TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- A compact chart has one coefficient constant for all regularized
weights, obtained by applying the fixed-background native estimate to the
actual scalar-multiplied forms. -/
theorem exists_regularized_coefficient_bound (g : Yau.SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : Metric (M := M) E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (Φ : M.Carrier → ℝ) (hΦ : SmoothFn Φ)
    (p : ℕ → M.Carrier → ℝ) (hp : ∀ j, SmoothFn (p j))
    (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
    (hs : K ⊆ localDomain (r := r) E a) (α : Fin r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : NQForm E 0), LocallyL2 (r := r) E u → ∀ j : ℕ,
      (∫⁻ z in K, ENNReal.ofReal (‖coefficients (r := r) E u a z Fin.elim0 α‖ ^ 2 *
        Real.exp (-p j (chartInv a z))) ∂lebesgueC n) ≤
        ENNReal.ofReal C * weightedNormSq (r := r) E g.form h μ (fun x => Φ x + p j x) u := by
  obtain ⟨C, hC, hb⟩ := compact_top_coefficient_integral_bound E g μ hμ h hh Φ hΦ a K hK hs α
  refine ⟨C, hC, ?_⟩
  intro u hu j
  let η : M.Carrier → ℂ := fun x => poleMultiplier (p j) x
  have hη (a : M.Carrier) : ContinuousOn (inChart a η) (localDomain (r := r) E a) := by
    exact Complex.continuous_ofReal.comp_continuousOn
      (((poleMultiplier_smooth (p j) (hp j)) a).continuousOn.mono Set.inter_subset_left)
  have hlocal := locallyL2_multiplyForm E η hη u hu
  have hn := hb (multiplyForm E η u) hlocal
  rw [multiply_top_weight_identity E g μ h Φ (p j) u] at hn
  have he : (∫⁻ z in K, ENNReal.ofReal
        (‖coefficients (r := r) E (multiplyForm E η u) a z Fin.elim0 α‖ ^ 2) ∂lebesgueC n) =
      ∫⁻ z in K, ENNReal.ofReal (‖coefficients (r := r) E u a z Fin.elim0 α‖ ^ 2 *
        Real.exp (-p j (chartInv a z))) ∂lebesgueC n := by
    apply lintegral_congr
    intro z
    rw [coefficients_multiplyForm, norm_mul, mul_pow]
    have hsq : poleMultiplier (p j) (chartInv a z) ^ 2 = Real.exp (-p j (chartInv a z)) := by
      simpa only [Pi.zero_apply, neg_zero, Real.exp_zero, mul_one, zero_add] using
        poleMultiplier_sq_weight (fun _ => 0) (p j) (chartInv a z)
    change ENNReal.ofReal (‖(poleMultiplier (p j) (chartInv a z) : ℂ)‖ ^ 2 * _) = _
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, hsq, mul_comm]
  exact he ▸ hn

end Yau.NodeProofs.P03Aux
