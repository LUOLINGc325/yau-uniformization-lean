import Yau.Proofs.V04PositiveReplacementAlgebra
import Yau.Proofs.V04PositiveReplacementPointwise
import Yau.Proofs.V04PositiveReplacementContinuity
import Yau.Proofs.V04ClockBoundaryWeights
import Yau.Proofs.V03BoundaryHermitian

/-! The four wall powers cancel in the original cost. The average error
uses the original same frame and the actual fixed-index clock weight. -/
open scoped Matrix Topology ContDiff ComplexOrder MatrixOrder
open MeasureTheory
noncomputable section
namespace Yau.Blueprint.V04Proof.PositiveReplacementAux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem circleAverage_abs_sub_bound {f g N : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hN : Continuous N) {C δ : ℝ}
    (hbound : ∀ θ, |f θ - g θ| ≤ C * (N θ + δ)) :
    |circleAverage f - circleAverage g| ≤ C * (circleAverage N + δ) := by
  have hsub : circleAverage f - circleAverage g = circleAverage (fun θ => f θ - g θ) := by
    unfold circleAverage
    rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
    ring
  rw [hsub]
  calc
    _ ≤ circleAverage (fun θ => |f θ - g θ|) := by
      unfold circleAverage
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 * Real.pi)⁻¹)]
      exact mul_le_mul_of_nonneg_left
        (intervalIntegral.abs_integral_le_integral_abs (by positivity : (0 : ℝ) ≤ 2 * Real.pi))
        (by positivity)
    _ ≤ circleAverage (fun θ => C * (N θ + δ)) := by
      unfold circleAverage
      exact mul_le_mul_of_nonneg_left
        (intervalIntegral.integral_mono_on (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
          ((hf.sub hg).abs.intervalIntegrable _ _)
          ((continuous_const.mul (hN.add continuous_const)).intervalIntegrable _ _)
          (fun θ _ => hbound θ)) (by positivity)
    _ = _ := by
      rw [circleAverage_const_mul, circleAverage_add_of_continuous hN continuous_const,
        circleAverage_const_value]

theorem boundarySymbol_bivectorCost {d : VariationData X q} (hd : VariationSetup d)
    {j a : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F)
    {E : ℂ → CotangentMatrix n} (hE : NormalizedDiscFrame d.G F.f E) (θ : ℝ) :
    bivectorCost (boundarySymbol d j a F E (circlePoint θ)) (frameBivector (E (circlePoint θ))) =
      wallPower d j a (F.f (circlePoint θ)) ^ 4 * symplecticP (boundaryHessian d j F (circlePoint θ)) := by
  unfold boundarySymbol frameBivector
  rw [← Complex.ofReal_pow, bivectorCost_real_smul, bivectorCost_congruence _ _ _
    (isUnit_iff_ne_zero.mpr (hE.1.1 _ (circlePoint_mem_closedBall θ))),
    bivectorCost_canonical _ (boundaryHessian_isHermitian hd hF θ)]
  ring

theorem clockSymplecticCost_eq_weighted_symbol {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} {j a : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F)
    {E : ℂ → CotangentMatrix n} (hE : NormalizedDiscFrame d.G F.f E) :
    clockSymplecticCost d k j a F = circleAverage (fun θ =>
      discTime F (circlePoint θ) / F.s * clockWeight d k j a F θ *
        (wallPower d j a (F.f (circlePoint θ)) ^ 4)⁻¹ *
        bivectorCost (boundarySymbol d j a F E (circlePoint θ)) (frameBivector (E (circlePoint θ)))) := by
  apply congrArg circleAverage
  funext θ
  rw [boundarySymbol_bivectorCost hd hF hE θ]
  have hm := pow_ne_zero 4 (admissible_wallPower_bounds hd hF a θ).1.ne'
  field_simp [(admissible_wallPower_bounds hd hF a θ).1.ne', hF.2.2.2.1.ne']

/-- The error coefficient is chosen before delta and before the family. -/
theorem fixed_index_weighted_replacement_bound {d : VariationData X q}
    (hd : VariationSetup d) {k : ClockData X} (hk : ClockCutoffs d k) {a : ℕ}
    (ha : 4 ≤ a) (hsymbol : SymbolBounds d a) (j : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 →
      ∀ (F : VariationDisc X) (E : ℂ → CotangentMatrix n) {W : ℝ},
      AdmissibleVariationDisc d j F → NormalizedDiscFrame d.G F.f E → 0 ≤ W →
      (∀ θ, 0 ≤ discTime F (circlePoint θ) / F.s * clockWeight d k j a F θ *
        (wallPower d j a (F.f (circlePoint θ)) ^ 4)⁻¹ ∧
        discTime F (circlePoint θ) / F.s * clockWeight d k j a F θ *
          (wallPower d j a (F.f (circlePoint θ)) ^ 4)⁻¹ ≤ W) →
      |clockSymplecticCost d k j a F - circleAverage (fun θ =>
        discTime F (circlePoint θ) / F.s * clockWeight d k j a F θ *
          (wallPower d j a (F.f (circlePoint θ)) ^ 4)⁻¹ *
          bivectorCost (smoothMajorant δ (boundarySymbol d j a F E (circlePoint θ)))
            (frameBivector (E (circlePoint θ))))| ≤
      W * L * (negativeTrace d j a F E 1 + δ) := by
  obtain ⟨L, hL, herr⟩ := fixed_index_matrix_replacement_bound hd hsymbol j
  refine ⟨L, hL, fun {δ} hδ hδ1 F E {W} hF hE hW hweight => ?_⟩
  let A : ℝ → CotangentMatrix n := fun θ => boundarySymbol d j a F E (circlePoint θ)
  let J : ℝ → CotangentMatrix n := fun θ => frameBivector (E (circlePoint θ))
  let w : ℝ → ℝ := fun θ => discTime F (circlePoint θ) / F.s * clockWeight d k j a F θ *
    (wallPower d j a (F.f (circlePoint θ)) ^ 4)⁻¹
  obtain ⟨M, hM, hsymbol⟩ := hsymbol j
  have hHerm : ∀ θ, (A θ).IsHermitian := fun θ => ((hsymbol F E hF hE).1 θ).1
  have hA : ∀ i l, Continuous (fun θ => A θ i l) := fun i l =>
    (boundarySymbol_trace_contDiff hd j a ha F hF E hE i l).continuous
  have hJ : ∀ i j, Continuous (fun θ => J θ i j) := fun i j =>
    (closedDisc_scalar_trace_contDiff (normalizedFrame_bivector_contDiffOn hE i j)).continuous
  have hm : Continuous (fun θ => wallPower d j a (F.f (circlePoint θ))) :=
    (closedDisc_real_trace_contDiff ((cotangentDisc_wallProduct_contDiffOn hd j hF.1).pow a)).continuous
  have hw : Continuous w :=
    (((admissible_discTime_trace_contDiff hF).continuous.div_const _).mul
      ((clockWeightRaw_contDiff hd hk hF).continuous.div_const
        (circleAverage (clockWeightRaw d k j a F)))).mul
      ((hm.pow 4).inv₀ (fun θ => pow_ne_zero 4 (admissible_wallPower_bounds hd hF a θ).1.ne'))
  have hLcont : ∀ i j, Continuous (fun θ => smoothMajorant δ (A θ) i j) :=
    smoothMajorant_entry_continuous_of_bound hδ hM hA hHerm
      (fun θ => ((hsymbol F E hF hE).1 θ).2)
  have hN := matrixNegative_trace_pow_continuous hA hHerm 1
  simp only [pow_one] at hN
  rw [clockSymplecticCost_eq_weighted_symbol hd hF hE]
  have hb := circleAverage_abs_sub_bound
    (hw.mul (bivectorCost_continuous hA hJ))
    (hw.mul (bivectorCost_continuous hLcont hJ)) hN
    (C := W * L) (δ := δ) (fun θ => ?_)
  · simpa only [negativeTrace, pow_one, A, J, w, Pi.mul_def] using hb
  · change |w θ * bivectorCost (A θ) (J θ) - w θ * bivectorCost (smoothMajorant δ (A θ)) (J θ)| ≤ _
    rw [← mul_sub, abs_mul, abs_of_nonneg (hweight θ).1]
    have hp := herr hδ hδ1 F E hF hE θ
    have hn : 0 ≤ (Matrix.trace (matrixNegative (A θ))).re + δ := by
      have hn := (Complex.nonneg_iff.mp (matrixNegative_posSemidef (A θ)).trace_nonneg).1
      positivity
    exact (mul_le_mul (hweight θ).2 hp (abs_nonneg _) hW).trans_eq (by ring)

end Yau.Blueprint.V04Proof.PositiveReplacementAux
