import Yau.Proofs.P04CanonicalSubharmonic
import Yau.Proofs.P04MeanValueAlgebra
import Yau.Proofs.P04ExponentialGrowth
import Yau.LeafProofs.L18Exact

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal ComplexOrder

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

/-- The original L18 mean-value estimate, actual L12 volume comparison and
the SAME finite canonical weighted norm give the original distance growth. -/
theorem canonical_growth_of_weighted_norm (g : SmoothMetric M)
    (hRic : ∀ x, (ricci g.form x).PosSemidef) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (o : M.Carrier)
    (S : CanonicalSection M) (hS : IsHolomorphicCanonical S) (ψ : M.Carrier → ℝ)
    (Cψ : ℝ) (hψ : ∀ y, ψ y ≤ Cψ*(1+distFrom g.form o y)) {k : ℝ} (hk : 0 ≤ k)
    (hfinite : (∫⁻ y, ENNReal.ofReal (canonicalNormSq g.form S y*Real.exp (-(k*ψ y))) ∂μ) < ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      canonicalNormSq g.form S x ≤ Real.exp (C*(1+distFrom g.form o x)) ∧
      Real.log (canonicalNormSq g.form S x) ≤ C*(1+distFrom g.form o x) := by
  let u := canonicalNormSq g.form S
  let I : ℝ≥0∞ := ∫⁻ y, ENNReal.ofReal (u y*Real.exp (-(k*ψ y))) ∂μ
  let v₀ := μ (distBall g.form o 1)
  have hvpos : 0 < v₀ := L18Aux.riemannianVolume_distBall_pos g μ hμ o (by norm_num)
  have hvfin : v₀ < ⊤ := L18Aux.riemannianVolume_distBall_lt_top g μ hμ o (by norm_num)
  have hvreal : 0 < v₀.toReal := ENNReal.toReal_pos hvpos.ne' hvfin.ne
  let C₀ := max Cψ 0+1
  have hC₀ : 0 < C₀ := by dsimp only [C₀]; positivity
  have hψ' (y : M.Carrier) : ψ y ≤ C₀*(1+distFrom g.form o y) := by
    apply (hψ y).trans
    apply mul_le_mul_of_nonneg_right
    · dsimp only [C₀]
      linarith [le_max_left Cψ 0]
    · have H := g.induced_distance_nonneg o y
      change 0 ≤ distFrom g.form o y at H
      linarith
  obtain ⟨L,hL,hmean⟩ := Yau.LeafProofs.L18 n (L12Aux.manifold_dimension_pos M)
  obtain ⟨huSmooth,huSub⟩ := canonicalNormSq_subharmonic g hRic S hS
  let A := L*(I.toReal+1)/v₀.toReal
  have hA : 0 < A := div_pos (mul_pos hL (by positivity)) hvreal
  let a := k*C₀
  have ha : 0 ≤ a := mul_nonneg hk hC₀.le
  have hpoint (x : M.Carrier) :
      u x ≤ A*Real.exp (a*(2+distFrom g.form o x))*(distFrom g.form o x+2)^(2*n) := by
    have hLM := hmean M g g.complete_distance g.kahler_equations hRic μ hμ u huSmooth huSub x 1 (by norm_num)
    have hlocal := unitBall_integral_le_weighted g μ o x u ψ
      (fun y => canonicalNormSq_nonneg g.form S y) hk hC₀.le hψ'
    have hweighted : ENNReal.ofReal (u x)*μ (distBall g.form x 1) ≤
        ENNReal.ofReal L*ENNReal.ofReal (Real.exp (a*(2+distFrom g.form o x)))*I := by
      calc
        _ ≤ ENNReal.ofReal L*(∫⁻ y in distBall g.form x 1, ENNReal.ofReal (u y) ∂μ) := hLM
        _ ≤ ENNReal.ofReal L*(ENNReal.ofReal (Real.exp (a*(2+distFrom g.form o x)))*I) :=
          mul_le_mul_right hlocal _
        _ = _ := (mul_assoc _ _ _).symm
    have hr : 0 ≤ distFrom g.form o x := g.induced_distance_nonneg o x
    exact point_bound_of_weighted_meanvalue (canonicalNormSq_nonneg g.form S x) hL.le
      (Real.exp_pos _).le (pow_nonneg (by linarith) _) I v₀ (μ (distBall g.form x 1))
      hfinite hvpos hvfin (origin_unitBall_volume_le g hRic μ hμ o x) hweighted
  obtain ⟨C,hC,hExp⟩ := polynomial_exp_le_linear_exp hA ha (2*n)
  refine ⟨C,hC,fun x => ?_⟩
  have hr : 0 ≤ distFrom g.form o x := g.induced_distance_nonneg o x
  have hbound := (hpoint x).trans (hExp _ hr)
  refine ⟨hbound,?_⟩
  by_cases hzero : u x=0
  · change Real.log (u x) ≤ _
    rw [hzero,Real.log_zero]
    exact mul_nonneg hC (by linarith)
  · have hp : 0 < u x := lt_of_le_of_ne (canonicalNormSq_nonneg g.form S x) (Ne.symm hzero)
    have H := Real.log_le_log hp hbound
    rwa [Real.log_exp] at H

end Yau.Proofs.P04Aux
