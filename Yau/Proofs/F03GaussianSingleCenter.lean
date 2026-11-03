import Yau.Proofs.F03GaussianDenominator
import Yau.Proofs.F03MinimalKernelGaussian

/-! The actual minimal kernel has a Gaussian upper bound with one center's actual ball volume. -/
noncomputable section
open MeasureTheory Set
open scoped ComplexOrder
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings LeafProofs.L18Aux LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem symmetric_gaussian_to_single_center
    (g : SmoothMetric M) (hcomplete : IsComplete g) (hK : IsKahler g)
    (hRic : ∀ z,(ricci g.form z).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (x y : M.Carrier) {r C c v : ℝ} (hr : 0 < r) (hC : 0 ≤ C) (hc : 0 < c)
    (hv : v ≤ C*Real.exp (-c*distFrom g.form x y^2/r^2)/
      Real.sqrt ((μ (distBall g.form x r)).toReal*(μ (distBall g.form y r)).toReal)) :
    v ≤ C*Real.exp ((n : ℝ)^2/(2*c))*Real.exp (-(c/2)*distFrom g.form x y^2/r^2)/
      (μ (distBall g.form x r)).toReal := by
  let q := inducedDistance g.form x y/r
  let V := (μ (distBall g.form x r)).toReal
  have hq : 0 ≤ q := div_nonneg (g.induced_distance_nonneg x y) hr.le
  have hV : 0 < V := ENNReal.toReal_pos
    (riemannianVolume_distBall_pos g μ hμ x hr).ne'
    (riemannianVolume_distBall_lt_top g μ hμ x hr).ne
  have hDen : 1/Real.sqrt ((μ (distBall g.form x r)).toReal*(μ (distBall g.form y r)).toReal) ≤
      (q+1)^n/V := by
    simpa only [q,V,add_comm] using gaussian_inverse_volume_denominator g hcomplete hK hRic μ hμ x y hr
  have hv' : v ≤ C*Real.exp (-c*q^2)*
      (1/Real.sqrt ((μ (distBall g.form x r)).toReal*(μ (distBall g.form y r)).toReal)) := by
    convert hv using 1
    dsimp [q,distFrom,lengthDist]
    rw [div_pow]
    ring
  have hPoly := polynomial_mul_gaussian_le n c hc q hq
  calc
    v ≤ C*Real.exp (-c*q^2)*
        (1/Real.sqrt ((μ (distBall g.form x r)).toReal*(μ (distBall g.form y r)).toReal)) := hv'
    _ ≤ C*Real.exp (-c*q^2)*((q+1)^n/V) :=
      mul_le_mul_of_nonneg_left hDen (mul_nonneg hC (Real.exp_pos _).le)
    _ = (C/V)*((q+1)^n*Real.exp (-c*q^2)) := by ring
    _ ≤ (C/V)*(Real.exp ((n : ℝ)^2/(2*c))*Real.exp (-(c/2)*q^2)) :=
      mul_le_mul_of_nonneg_left hPoly (div_nonneg hC hV.le)
    _ = _ := by
      dsimp [q,V,distFrom,lengthDist]
      rw [div_pow]
      ring

theorem dirichletMinimalKernelCandidate_single_center_gaussian
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) :
    ∃ C c : ℝ,0 < C ∧ 0 < c ∧
      ∀ (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
        (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) (t : ℝ),0 < t → ∀ x y,
      dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO t x y ≤
        C*Real.exp (-c*distFrom X.metric.form x y^2/t)/
          (μ (distBall X.metric.form x (Real.sqrt t))).toReal := by
  obtain ⟨C,c,_C₁,_c₁,hC,hc,_hC₁,_hc₁,hBound⟩ :=
    dirichletMinimalKernelCandidate_gaussian_gradient X o h U P ρ hf
  refine ⟨C*Real.exp ((n : ℝ)^2/(2*c)),c/2,mul_pos hC (Real.exp_pos _),by positivity,?_⟩
  intro μ hμ O hO t ht x y
  have hg : dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO t x y ≤
      C*Real.exp (-c*distFrom X.metric.form x y^2/(Real.sqrt t)^2)/
        Real.sqrt ((μ (distBall X.metric.form x (Real.sqrt t))).toReal*
          (μ (distBall X.metric.form y (Real.sqrt t))).toReal) := by
    simpa only [Real.sq_sqrt ht.le] using (hBound μ hμ O hO t ht x y).1
  have hh := symmetric_gaussian_to_single_center X.metric X.complete_metric X.kahler_metric
    (F02Aux.initialRicci_posSemidef X o h U P ρ hf) μ hμ x y
    (Real.sqrt_pos.mpr ht) hC.le hc hg
  simpa only [Real.sq_sqrt ht.le] using hh

end Yau.Proofs.F03Aux
