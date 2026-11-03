import Yau.LeafProofs.L16ExpBoundaryActualModulus
import Yau.LeafProofs.L16ExpBoundaryDataLipschitz

open Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.LeafProofs.L16ExpBoundaryAux

open Yau.Parabolic Yau.ParabolicCandidates

/-- The fixed data and actual initial/lateral barrier package for the original
exponential equation. All three choices precede the candidate solution. -/
theorem exp_boundary_fixed_data_and_barriers {n : ℕ} (hn : 0 < n)
    {O : Set (Space n)} (hO : SmoothDomain O)
    {T lam upper m B : ℝ} (hT : 0 < T) (hm : 0 < m) (hmB : m ≤ B)
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {R p : Point n → ℝ}
    (hab : SmoothCoefficients (cylinder (closure O) 0 T) a b)
    (hR : ContDiffOn ℝ ∞ R (cylinder (closure O) 0 T))
    (hp : ContDiffOn ℝ ∞ p (cylinder (closure O) 0 T))
    (he : Elliptic (cylinder (closure O) 0 T) a lam upper) :
    ∃ (G : Point n → ℝ) (K L : ℝ), 0 < K ∧ 0 < L ∧
      ContDiffOn ℝ ∞ G (cylinder (closure O) 0 T) ∧
      (∀ z ∈ cylinder (closure O) 0 T, |G z| ≤ L) ∧
      (∀ z ∈ cylinder (closure O) 0 T, ∀ w ∈ cylinder (closure O) 0 T,
        |G z-G w| ≤ L*(‖z.1-w.1‖+|z.2-w.2|)) ∧
      ∀ q : Point n → ℝ, C2 (cylinder (closure O) 0 T) q →
        (∀ z ∈ cylinder (closure O) 0 T, m ≤ q z ∧ q z ≤ B) →
        DirichletData O T q p → ExpDivergenceEquation (O ×ˢ Ioc 0 T) a b R q →
        DirichletData O T q G ∧
        ∀ z ∈ cylinder (closure O) 0 T,
          |q z-G z| ≤ K*min z.2 (Metric.infDist z.1 (frontier O)) := by
  obtain ⟨ℓ,K,hK,hℓ,hℓeq,hG,hbar⟩ := actual_boundary_initial_modulus hn hO hT hm hmB hab hR hp he
  let G : Point n → ℝ := fun z => Real.exp (ℓ (p z))
  obtain ⟨J,hLip⟩ := smoothDomain_closed_cylinder_lipschitz hO hG
  obtain ⟨C,hC⟩ := (hO.2.2.1.prod isCompact_Icc).exists_bound_of_continuousOn hG.continuousOn
  let L : ℝ := 1+(J : ℝ)+|C|
  have hJ : 0 ≤ (J : ℝ) := J.property
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨G,K,L,hK,hL,hG,?_,?_,hbar⟩
  · intro z hz
    have hzC : |G z| ≤ C := by simpa only [Real.norm_eq_abs] using hC z hz
    exact hzC.trans (by dsimp [L]; linarith [le_abs_self C])
  · intro z hz w hw
    have hdist : |G z-G w| ≤ (J : ℝ)*max ‖z.1-w.1‖ |z.2-w.2| := by
      change |Real.exp (ℓ (p z))-Real.exp (ℓ (p w))| ≤ (J : ℝ)*max ‖z.1-w.1‖ |z.2-w.2|
      simpa only [dist_eq_norm,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,Real.norm_eq_abs] using
        hLip.dist_le_mul z hz w hw
    have hmax : max ‖z.1-w.1‖ |z.2-w.2| ≤ ‖z.1-w.1‖+|z.2-w.2| :=
      max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
    have hJL : (J : ℝ) ≤ L := by dsimp [L]; linarith [abs_nonneg C]
    exact hdist.trans ((mul_le_mul_of_nonneg_left hmax hJ).trans
      (mul_le_mul_of_nonneg_right hJL (by positivity)))

end Yau.LeafProofs.L16ExpBoundaryAux
