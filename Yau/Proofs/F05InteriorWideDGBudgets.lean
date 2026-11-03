import Yau.Proofs.F05HolderCaps
import Yau.Proofs.F05HolderCompactCoefficients
import Yau.LeafProofs.L16ExpBoundaryHolderCoefficients

/-! Fixed full interior buffers retain the actual DG drift b-div(a),
positive matrix a/q and forcing (q-1)R on the radius-eleven-quarters cap. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.ParabolicCandidates Yau.F05Transport Yau.LeafProofs.L16Aux
open Yau.LeafProofs.L16ExpBoundaryHolderAux
variable {n : ℕ}

theorem F05_exp_wide_DG_budgets (k : Option (RIdx n)) {S lam upper m B : ℝ}
    (hm : 0 < m) (hmB : m ≤ B)
    {a : Point n → Mat n} {b : Point n → RIdx n → ℝ} {R : Point n → ℝ}
    (hab : SmoothCoefficients (Metric.ball 0 3 ×ˢ Icc 0 S) a b)
    (hR : ContDiffOn ℝ ∞ R (Metric.ball 0 3 ×ˢ Icc 0 S))
    (he : Elliptic (cylinder (Metric.closedBall 0 (11/4)) 0 S) a lam upper) :
    ∃ D F : ℝ, 0 < D ∧ 0 < F ∧ ∀ (T : ℝ), 0 < T → T ≤ S →
      ∀ q : Point n → ℝ,
      (∀ z ∈ cylinder (region k (11/4)) 0 T, m ≤ q z ∧ q z ≤ B) →
      DGUniformBounds (F05CapOpen k (11/4) ×ˢ Ioo 0 T)
        (expDGMatrix a q) (expDGDrift a b q) (expDGForcing R q)
        (lam/B) (upper/m) D F := by
  let K : Set (Point n) := Metric.closedBall 0 (11/4) ×ˢ Icc 0 S
  let U : Set (Point n) := Metric.ball 0 (11/4) ×ˢ Ioo 0 S
  have hK : IsCompact K := (isCompact_closedBall (0 : Space n) (11/4)).prod isCompact_Icc
  have hU : IsOpen U := Metric.isOpen_ball.prod isOpen_Ioo
  have hUK : U ⊆ K := fun _ hz => ⟨Metric.ball_subset_closedBall hz.1,Ioo_subset_Icc_self hz.2⟩
  have hKU : K ⊆ Metric.ball (0 : Space n) 3 ×ˢ Icc 0 S := fun _ hz =>
    ⟨Metric.closedBall_subset_ball (by norm_num : ((11/4) : ℝ) < 3) hz.1,hz.2⟩
  obtain ⟨A₀,D₀,hA₀,hD₀,hA,hDrift⟩ := F05_compact_coefficient_bounds hK hU hUK
    ⟨hab.1.mono hKU,fun i => (hab.2 i).mono hKU⟩
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn (hR.continuousOn.mono hKU)
  let R₀ := 1+|C|
  have hR₀ : 0 < R₀ := by dsimp [R₀]; positivity
  have hB : 0 < B := hm.trans_le hmB
  refine ⟨D₀/m,(B+1)*R₀,by positivity,by positivity,?_⟩
  intro T hT hTS q hbound
  have hQK : cylinder (region k (11/4)) 0 T ⊆ K := by
    intro z hz
    exact ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hz.1.1,
      hz.2.1,hz.2.2.trans hTS⟩
  have hOpenK : F05CapOpen k (11/4) ×ˢ Ioo 0 T ⊆ cylinder (region k (11/4)) 0 T :=
    fun _ hz => ⟨F05CapOpen_closure_subset k (11/4) (subset_closure hz.1),Ioo_subset_Icc_self hz.2⟩
  have hOpenU : F05CapOpen k (11/4) ×ˢ Ioo 0 T ⊆ U := fun _ hz =>
    ⟨hz.1.2,hz.2.1,hz.2.2.trans_le hTS⟩
  have hEllBase : Elliptic (cylinder (region k (11/4)) 0 T) a lam upper :=
    ⟨he.1,he.2.1,fun z hz => he.2.2 z (hQK hz)⟩
  have hEll := elliptic_div_of_bounds hEllBase hm hmB hbound
  refine ⟨⟨hEll.1,hEll.2.1,fun z hz => hEll.2.2 z (hOpenK hz)⟩,?_,?_⟩
  · intro z hz
    have hqSq : m^2 ≤ (q z)^2 := pow_le_pow_left₀ hm.le (hbound z (hOpenK hz)).1 2
    have hsum : (∑ i, (energyDrift a b z i)^2) ≤ D₀^2 := by
      simpa only [sq_abs] using hDrift z (hOpenU hz)
    have hboundDiv : (∑ i, (energyDrift a b z i)^2)/(q z)^2 ≤ D₀^2/m^2 :=
      (div_le_div_of_nonneg_right hsum (sq_nonneg _)).trans
        (div_le_div_of_nonneg_left (sq_nonneg D₀) (sq_pos_of_pos hm) hqSq)
    simpa only [dgGradientSq,expDGDrift,div_pow,Finset.sum_div] using hboundDiv
  · intro z hz
    have hzQ := hOpenK hz
    have hqpos : 0 < q z := hm.trans_le (hbound z hzQ).1
    have hqabs : |q z-1| ≤ B+1 := by
      have h := abs_sub (q z) (1 : ℝ)
      rw [abs_of_pos hqpos,abs_one] at h
      exact h.trans (add_le_add (hbound z hzQ).2 le_rfl)
    have hRF : |R z| ≤ R₀ := by
      have hh : |R z| ≤ C := by simpa only [Real.norm_eq_abs] using hC z (hQK hzQ)
      exact hh.trans (by dsimp [R₀]; linarith [le_abs_self C])
    exact (abs_mul _ _).trans_le (mul_le_mul hqabs hRF (abs_nonneg _) (by positivity))

end Yau.Proofs.F05Aux
