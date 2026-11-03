import Yau.Proofs.F04CutoffIntegralBounds
import Yau.Proofs.F04BottomTimeLimit
import Yau.Proofs.F04ClassicalWeakEquation

open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.F04Proof

open Yau.Parabolic Yau.LeafProofs.L16Aux

/-- The bottom slice vanishes using only the actual O(t) value bound.
The coefficient and cutoff factor is independent of K and of the solution. -/
theorem initial_gradient_cutoff_bound {n : ℕ} {O : Set (Space n)}
    (hO : IsOpen O) (hOc : IsCompact (closure O)) {S s ν L D M : ℝ}
    (hs : 0 < s) (hsS : s < S) (hν : 0 < ν) (hD : 0 ≤ D) (hM : 0 ≤ M)
    {A : Point n → Mat n} {c : Point n → Yau.RIdx n → ℝ} {η : Space n → ℝ}
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hηO : tsupport η ⊆ O)
    (hηrange : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    (hηM : ∀ x, (∑ i, (d η x i) ^ 2) + (η x) ^ 2 ≤ M)
    {K : ℝ} (hK : 0 ≤ K) {u : Point n → ℝ}
    (hf : DGClassicalFields (O ×ˢ Ioo 0 S) A c (fun _ => 0) u)
    (hpde : ClassicalDivEq (O ×ˢ Ioo 0 S) A c (fun _ => 0) u)
    (hb : DGUniformBounds (O ×ˢ Ioo 0 S) A c (fun _ => 0) ν L D 0)
    (hbound : ∀ x ∈ O, ∀ t ∈ Ioo 0 s, |u (x, t)| ≤ K * t) :
    Integrable (fun p => dgGradientSq (dgGradient u p) * (η p.1) ^ 2) (productVolume O (Ioo 0 s)) ∧
      dgCylinderIntegral O 0 s (fun p => dgGradientSq (dgGradient u p) * (η p.1) ^ 2) ≤
        ((2 + 8 * L ^ 2 / ν + 2 * D ^ 2 / ν) * M * volume.real O / ν) * K ^ 2 * s ^ 3 := by
  let H : Point n → ℝ := fun p => dgGradientSq (dgGradient u p) * (η p.1) ^ 2
  let C0 : ℝ := 2 + 8 * L ^ 2 / ν + 2 * D ^ 2 / ν
  let B : ℝ := (C0 * M * volume.real O / ν) * K ^ 2 * s ^ 3
  let E0 : ℝ := K ^ 2 * volume.real O / ν
  have hC0 : 0 ≤ C0 := by dsimp only [C0]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hE0 : 0 ≤ E0 := by dsimp only [E0]; positivity
  have hsub : O ×ˢ Ioo (0 : ℝ) s ⊆ O ×ˢ Ioo 0 S :=
    fun p hp => ⟨hp.1, hp.2.1, hp.2.2.trans hsS⟩
  have hgrad (i : Yau.RIdx n) : ContinuousOn (fun p => dgGradient u p i) (O ×ˢ Ioo 0 s) :=
    ((dgGradient_contDiffOn (hO.prod isOpen_Ioo) hf.2.2.2 i).continuousOn).mono hsub
  have hCont : ContinuousOn H (O ×ˢ Ioo 0 s) :=
    (continuousOn_finsetSum _ (fun i _ => (hgrad i).pow 2)).mul
      ((hη.continuous.comp continuous_fst).pow 2).continuousOn
  have hmeas : AEStronglyMeasurable H (productVolume O (Ioo 0 s)) := by
    rw [dg_productVolume_eq_restrict]
    exact hCont.aestronglyMeasurable (hO.prod isOpen_Ioo).measurableSet
  apply bottom_time_integral_bound hO hs hB hE0 hmeas
    (.of_forall (fun p => mul_nonneg (dgGradientSq_nonneg _) (sq_nonneg _)))
  intro δ hδ
  have hu : ContinuousOn u (O ×ˢ Icc δ s) := hf.2.2.2.continuousOn.mono
    (fun p hp => ⟨hp.1, hδ.1.trans_le hp.2.1, hp.2.2.trans_lt hsS⟩)
  have hfinite := full_gradient_cutoff_energy hO hδ.1 hδ.2 hsS hν hD hf hpde hb hu
    (timeConstant_spatial_cutoff hη hcη hηO hηrange δ s)
  have hval := timeConstant_cutoff_integral_bounds hO hOc hδ hK hM hηrange hηM hbound
  refine ⟨hfinite.1, ?_⟩
  have hupper : ν * dgCylinderIntegral O δ s H ≤
      C0 * ((K * s) ^ 2 * M * volume.real O * s) + (K * δ) ^ 2 * volume.real O := by
    exact hfinite.2.trans (add_le_add (mul_le_mul_of_nonneg_left hval.1 hC0) hval.2)
  apply (mul_le_mul_iff_right₀ hν).mp
  calc
    ν * dgCylinderIntegral O δ s H ≤ _ := hupper
    _ = ν * (B + E0 * δ ^ 2) := by
      dsimp only [B, E0]
      field_simp

end Yau.F04Proof
