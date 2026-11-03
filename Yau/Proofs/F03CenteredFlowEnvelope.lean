import Yau.Proofs.F03CenteredFlowPotential

/-! One actual terminal density dominates the centered potential and its physical-time derivative. -/
noncomputable section
open Set
namespace Yau.Proofs.F03Aux
open Yau Blueprint
variable {n : ℕ}

theorem centeredFlowPotential_endpoint_zero
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 < T) (x : Pt X) :
    centeredFlowPotential X U T x 0=0 ∧ centeredFlowPotential X U T x T=0 := by
  simp [centeredFlowPotential,hf.2.2.2.2.2.2.1 x,hT.ne']

theorem centeredFlowPotential_terminal_envelope
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 < T)
    {s : ℝ} (hs : s ∈ Icc 0 T) (x : Pt X) :
    |centeredFlowPotential X U T x s| ≤ 2*T*ρ x T ∧
      |P x s-U x T/T| ≤ 2*ρ x T := by
  have hSource := localizedFlow_potential_time_envelope X o h U P ρ hf hs x
  have hTerminal := localizedFlow_potential_time_envelope X o h U P ρ hf ⟨hT.le,le_rfl⟩ x
  have hq0 : 0 ≤ s/T := div_nonneg hs.1 hT.le
  have hq1 : s/T ≤ 1 := (div_le_one hT).mpr hs.2
  constructor
  · have hTriangle : |centeredFlowPotential X U T x s| ≤ |U x s|+(s/T)*|U x T| := by
      simpa only [centeredFlowPotential,sub_eq_add_neg,abs_neg,abs_mul,abs_of_nonneg hq0] using
        abs_add_le (U x s) (-((s/T)*U x T))
    have hSmall := mul_le_of_le_one_left (abs_nonneg (U x T)) hq1
    nlinarith
  · have hDiv : |U x T/T| ≤ ρ x T := by
      rw [abs_div,abs_of_pos hT]
      exact (div_le_iff₀ hT).mpr (by simpa only [mul_comm] using hTerminal.2)
    have hTriangle : |P x s-U x T/T| ≤ |P x s|+|U x T/T| := by
      simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (P x s) (-(U x T/T))
    linarith

end Yau.Proofs.F03Aux
