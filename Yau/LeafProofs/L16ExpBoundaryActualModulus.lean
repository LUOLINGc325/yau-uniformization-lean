import Yau.LeafProofs.L16ExpBoundaryReduction

open Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.LeafProofs.L16ExpBoundaryAux

open Yau.Parabolic Yau.ParabolicCandidates

/-- Actual boundary and initial barriers for the frozen exponential equation.
The smooth data transform and the one constant precede every candidate q. -/
theorem actual_boundary_initial_modulus {n : ℕ} (hn : 0 < n)
    {O : Set (Space n)} (hO : SmoothDomain O)
    {T lam upper m B : ℝ} (hT : 0 < T) (hm : 0 < m) (hmB : m ≤ B)
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {R p : Point n → ℝ}
    (hab : SmoothCoefficients (cylinder (closure O) 0 T) a b)
    (hR : ContDiffOn ℝ ∞ R (cylinder (closure O) 0 T))
    (hp : ContDiffOn ℝ ∞ p (cylinder (closure O) 0 T))
    (he : Elliptic (cylinder (closure O) 0 T) a lam upper) :
    ∃ (ℓ : ℝ → ℝ) (K : ℝ), 0 < K ∧ ContDiff ℝ ∞ ℓ ∧
      EqOn ℓ Real.log (Ioo (m/2) (B+1)) ∧
      ContDiffOn ℝ ∞ (fun z => Real.exp (ℓ (p z))) (cylinder (closure O) 0 T) ∧
      ∀ q : Point n → ℝ, C2 (cylinder (closure O) 0 T) q →
        (∀ z ∈ cylinder (closure O) 0 T, m ≤ q z ∧ q z ≤ B) →
        DirichletData O T q p → ExpDivergenceEquation (O ×ˢ Ioc 0 T) a b R q →
        DirichletData O T q (fun z => Real.exp (ℓ (p z))) ∧
        ∀ z ∈ cylinder (closure O) 0 T,
          |q z-Real.exp (ℓ (p z))| ≤ K*min z.2 (Metric.infDist z.1 (frontier O)) := by
  obtain ⟨ℓ,A₁,b₁,H,W₀,E,hA₁,hb₁,hH,hW₀,hE,hℓ,hℓeq,hG,hred⟩ :=
    actual_log_boundary_reduction hO hT hm hmB hab hR hp he
  have hν : 0 < lam/B := div_pos he.1 (hm.trans_le hmB)
  obtain ⟨K₁,hK₁,hspatial⟩ := smoothDomain_uniform_boundary_distance_modulus hn hO
    (upper := upper/m) hT hν hA₁.le hb₁.le hH hW₀
  let K : ℝ := E*(H+K₁+1)
  have hK : 0 < K := by dsimp [K]; positivity
  have hEH : E*H ≤ K := by dsimp [K]; nlinarith
  have hEK : E*K₁ ≤ K := by dsimp [K]; nlinarith
  refine ⟨ℓ,K,hK,hℓ,hℓeq,hG,?_⟩
  intro q hq hbound hdata heq
  obtain ⟨hctrl,htransfer⟩ := hred q hq hbound hdata heq
  have htime : ∀ z ∈ cylinder (closure O) 0 T,
      |Real.log (q z)-ℓ (p z)| ≤ H*z.2 := by
    rcases hctrl with ⟨hEll,hA,hb,hc,hs,ht,hi,hl,hsup,hop⟩
    exact initial_barrier_abs_openTop hO.1 hO.2.2.1 hT hH.le hc hs ht hEll hi hl hop
  have hdist := hspatial _ _ _ hctrl
  refine ⟨(fixed_log_boundary_agreement hT.le hm hℓeq hbound hdata).1,?_⟩
  intro z hz
  have htimeq : |q z-Real.exp (ℓ (p z))| ≤ K*z.2 := calc
    _ ≤ E*|Real.log (q z)-ℓ (p z)| := htransfer z hz
    _ ≤ E*(H*z.2) := mul_le_mul_of_nonneg_left (htime z hz) hE.le
    _ = (E*H)*z.2 := by ring
    _ ≤ K*z.2 := mul_le_mul_of_nonneg_right hEH hz.2.1
  have hdistq : |q z-Real.exp (ℓ (p z))| ≤ K*Metric.infDist z.1 (frontier O) := calc
    _ ≤ E*|Real.log (q z)-ℓ (p z)| := htransfer z hz
    _ ≤ E*(K₁*Metric.infDist z.1 (frontier O)) := mul_le_mul_of_nonneg_left (hdist z hz) hE.le
    _ = (E*K₁)*Metric.infDist z.1 (frontier O) := by ring
    _ ≤ K*Metric.infDist z.1 (frontier O) :=
      mul_le_mul_of_nonneg_right hEK Metric.infDist_nonneg
  by_cases hmin : z.2 ≤ Metric.infDist z.1 (frontier O)
  · rw [min_eq_left hmin]
    exact htimeq
  · rw [min_eq_right (le_of_not_ge hmin)]
    exact hdistq

end Yau.LeafProofs.L16ExpBoundaryAux
