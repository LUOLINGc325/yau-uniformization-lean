import Yau.LeafProofs.L16ExpBoundaryData
import Yau.LeafProofs.L16ExpBoundaryDataLipschitz

/-! Compact fixed-data bounds on the whole coordinate ball. These estimates
do not treat a cap with an artificial rim as a smooth Dirichlet domain. -/

open Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux Yau.LeafProofs.L16ExpBoundaryAux
variable {n : ℕ}

theorem F05_compact_fixed_data_bounds {K U : Set (Point n)} {P : Point n → ℝ}
    (hK : IsCompact K) (hU : IsOpen U) (hUK : U ⊆ K) (hP : ContDiffOn ℝ ∞ P K) :
    ∃ P₀ P₁ P₂ : ℝ, 0 < P₀ ∧ 0 < P₁ ∧ 0 < P₂ ∧
      (∀ z ∈ K, |P z| ≤ P₀) ∧
      (∀ z ∈ U, ‖fderiv ℝ P z‖ ≤ P₁) ∧
      ∀ z ∈ U, ‖fderiv ℝ (fderiv ℝ P) z‖ ≤ P₂ := by
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hP.continuousOn
  obtain ⟨P₁,hP₁,hFirst⟩ := bounded_fderiv_on_open_subset_of_compact
    hK hU hUK (hP.of_le (by simp))
  obtain ⟨P₂,hP₂,hSecond⟩ := bounded_secondFDeriv_on_open_subset_of_compact
    hK hU hUK (hP.of_le (by simp))
  refine ⟨1+|C|,P₁,P₂,by positivity,hP₁,hP₂,?_,hFirst,hSecond⟩
  intro z hz
  have hzC : |P z| ≤ C := by simpa only [Real.norm_eq_abs] using hC z hz
  exact hzC.trans (by linarith [le_abs_self C])

theorem F05_clipped_log_ball_data {S m B : ℝ} (hm : 0 < m) (hmB : m ≤ B)
    {p : Point n → ℝ} (hp : ContDiffOn ℝ ∞ p (Metric.ball 0 3 ×ˢ Icc 0 S)) :
    ∃ (ℓ : ℝ → ℝ) (P₀ P₁ P₂ L : ℝ),
      ContDiff ℝ ∞ ℓ ∧ HasCompactSupport ℓ ∧
      EqOn ℓ Real.log (Ioo (m/2) (B+1)) ∧
      0 < P₀ ∧ 0 < P₁ ∧ 0 < P₂ ∧ 0 < L ∧
      (∀ z ∈ Metric.closedBall (0 : Space n) 2 ×ˢ Icc 0 S, |ℓ (p z)| ≤ P₀) ∧
      (∀ z ∈ Metric.ball (0 : Space n) 2 ×ˢ Ioo 0 S,
        ‖fderiv ℝ (fun y => ℓ (p y)) z‖ ≤ P₁) ∧
      (∀ z ∈ Metric.ball (0 : Space n) 2 ×ˢ Ioo 0 S,
        ‖fderiv ℝ (fderiv ℝ (fun y => ℓ (p y))) z‖ ≤ P₂) ∧
      ∀ z ∈ Metric.closedBall (0 : Space n) 2 ×ˢ Icc 0 S,
        ∀ w ∈ Metric.closedBall (0 : Space n) 2 ×ˢ Icc 0 S,
        |Real.exp (ℓ (p z))-Real.exp (ℓ (p w))| ≤
          L*(‖z.1-w.1‖+|z.2-w.2|) := by
  obtain ⟨ℓ,hℓ,hSupport,hEq,hGerm⟩ := Yau.LeafProofs.L16Log.exists_smooth_log_transform hm hmB
  let K : Set (Point n) := Metric.closedBall 0 2 ×ˢ Icc 0 S
  let U : Set (Point n) := Metric.ball 0 2 ×ˢ Ioo 0 S
  have hCompact : IsCompact K := (isCompact_closedBall (0 : Space n) 2).prod isCompact_Icc
  have hOpen : IsOpen U := Metric.isOpen_ball.prod isOpen_Ioo
  have hUK : U ⊆ K := fun _ hz => ⟨Metric.ball_subset_closedBall hz.1,Ioo_subset_Icc_self hz.2⟩
  have hKU : K ⊆ Metric.ball (0 : Space n) 3 ×ˢ Icc 0 S := fun _ hz =>
    ⟨Metric.closedBall_subset_ball (by norm_num : (2 : ℝ) < 3) hz.1,hz.2⟩
  have hP := hℓ.comp_contDiffOn (hp.mono hKU)
  obtain ⟨P₀,P₁,P₂,hP₀,hP₁,hP₂,hValue,hFirst,hSecond⟩ :=
    F05_compact_fixed_data_bounds hCompact hOpen hUK hP
  have hG : ContDiffOn ℝ ∞ (fun z => Real.exp (ℓ (p z))) K := hP.exp
  obtain ⟨L,hLip⟩ := hG.exists_lipschitzOnWith (by simp)
    ((convex_closedBall (0 : Space n) 2).prod (convex_Icc 0 S)) hCompact
  refine ⟨ℓ,P₀,P₁,P₂,1+L,hℓ,hSupport,hEq,hP₀,hP₁,hP₂,by positivity,
    hValue,hFirst,hSecond,?_⟩
  intro z hz w hw
  have hh := hLip.norm_sub_le hz hw
  have hMax : ‖z-w‖ ≤ ‖z.1-w.1‖+|z.2-w.2| := by
    simp only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,Real.norm_eq_abs]
    exact max_le_add_of_nonneg (norm_nonneg _) (abs_nonneg _)
  calc
    _ ≤ (L : ℝ)*‖z-w‖ := by simpa only [Real.norm_eq_abs] using hh
    _ ≤ (L : ℝ)*(‖z.1-w.1‖+|z.2-w.2|) := mul_le_mul_of_nonneg_left hMax L.coe_nonneg
    _ ≤ (1+L)*(‖z.1-w.1‖+|z.2-w.2|) := by
      nlinarith [norm_nonneg (z.1-w.1),abs_nonneg (z.2-w.2)]

end Yau.Proofs.F05Aux
