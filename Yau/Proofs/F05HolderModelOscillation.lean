import Yau.Proofs.F05HolderDGBudgets
import Yau.Proofs.F05HolderEquationRestriction
import Yau.LeafProofs.L16ExpBoundaryHolderInteriorControl

/-! The native DG core applies to the exact model fields on the physical
region. The forcing and radius are fixed before every candidate and T. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.ParabolicCandidates Yau.F05Transport Yau.LeafProofs.L16Aux
open Yau.LeafProofs.L16ExpBoundaryHolderAux
variable {n : ℕ}

theorem F05_exp_model_oscillation (k : Option (RIdx n)) {S lam upper m B γ Cdg : ℝ}
    (hm : 0 < m) (hmB : m ≤ B)
    (hCore : InteriorOscillationEstimate n (lam/B) (upper/m) γ Cdg)
    {a : Point n → Mat n} {b : Point n → RIdx n → ℝ} {R : Point n → ℝ}
    (hab : SmoothCoefficients (Metric.ball 0 3 ×ˢ Icc 0 S) a b)
    (hR : ContDiffOn ℝ ∞ R (Metric.ball 0 3 ×ˢ Icc 0 S))
    (he : Elliptic (cylinder (Metric.closedBall 0 2) 0 S) a lam upper) :
    ∃ F ρ : ℝ, 0 < F ∧ 0 < ρ ∧ ρ ≤ 1/8 ∧ ∀ (T : ℝ), 0 < T → T ≤ S →
      ∀ q : Point n → ℝ, C2 (cylinder (region k 2) 0 T) q →
      ContDiffOn ℝ ∞ q (F05CapOpen k 3 ×ˢ Ioc 0 T) →
      (∀ z ∈ cylinder (region k 2) 0 T, m ≤ q z ∧ q z ≤ B) →
      ExpDivergenceEquation (F05CapOpen k 3 ×ˢ Ioc 0 T) a b R q →
      LocalOscillationControl (F05CapOpen k 2) T γ Cdg F ρ q := by
  obtain ⟨D,F,hD,hF,hBudget⟩ := F05_exp_model_DG_budgets k hm hmB hab hR he
  let ρ : ℝ := min (1/8) (dgOscDriftRadius D)
  have hρ : 0 < ρ := lt_min (by norm_num) (dgOscDriftRadius_pos hD.le)
  refine ⟨F,ρ,hF,hρ,min_le_left _ _,?_⟩
  intro T hT hTS q hq hqSmooth hbound heq
  have hClosed : cylinder (closure (F05CapOpen k 2)) 0 T ⊆ cylinder (region k 2) 0 T :=
    fun _ hz => ⟨F05CapOpen_closure_subset k 2 hz.1,hz.2⟩
  have hData : cylinder (closure (F05CapOpen k 2)) 0 T ⊆ Metric.ball (0 : Space n) 3 ×ˢ Icc 0 S := by
    intro z hz
    have hz2 := hClosed hz
    refine ⟨?_,hz.2.1,hz.2.2.trans hTS⟩
    rw [Metric.mem_ball,dist_zero_right]
    linarith [hz2.1.1]
  have hSmooth : SmoothCoefficients (cylinder (closure (F05CapOpen k 2)) 0 T) a b :=
    ⟨hab.1.mono hData,fun i => (hab.2 i).mono hData⟩
  have hQ : ContDiffOn ℝ ∞ q (F05CapOpen k 2 ×ˢ Ioc 0 T) := hqSmooth.mono
    (fun _ hz => ⟨F05_cap_radius_mono k (r := 2) (R := 3) (by norm_num) hz.1,hz.2⟩)
  have hFields := expDivergence_classical_fields (F05CapOpen_isOpen k 2) hm hSmooth
    (hR.mono hData) hQ (fun z hz => (hbound z (hClosed hz)).1)
  have hPDE := expDivergence_classical
    (F05_exp_equation_mono_space (F05_cap_radius_mono k (r := 2) (R := 3) (by norm_num)) heq)
  exact localOscillationControl_of_DG hCore hD.le hF.le (min_le_right _ _)
    hFields hPDE (hBudget T hT hTS q hbound) (hq.1.mono hClosed)

end Yau.Proofs.F05Aux
