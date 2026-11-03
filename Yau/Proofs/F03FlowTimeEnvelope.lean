import Yau.Proofs.F03MetricDefectHeat

/-! The original flow itself supplies one actual pointwise dominating density on every closed slab. -/
noncomputable section
open Set
namespace Yau.Proofs.F03Aux
open Yau Blueprint
variable {n : ℕ}

theorem localizedFlow_rho_terminal_bound
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {T s : ℝ} (hs : s ∈ Icc 0 T) (x : Pt X) :
    0 ≤ ρ x s ∧ ρ x s ≤ ρ x T := by
  exact ⟨(hf.2.2.2.2.2.2.2.2.2.1 x s hs.1).2,
    F02Aux.rho_monotoneOn X o h U P ρ hf x hs.1 (hs.1.trans hs.2) hs.2⟩

theorem localizedFlow_P_abs_eq_rho
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {s : ℝ} (hs : 0 ≤ s) (x : Pt X) : |P x s|=ρ x s := by
  have hr := hf.2.2.2.2.2.2.2.2.2.1 x s hs
  rw [hr.1,abs_of_nonpos (by linarith : P x s ≤ 0)]

theorem localizedFlow_potential_time_envelope
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {T s : ℝ} (hs : s ∈ Icc 0 T) (x : Pt X) :
    |P x s| ≤ ρ x T ∧ |U x s| ≤ T*ρ x T := by
  have hρ := localizedFlow_rho_terminal_bound X o h U P ρ hf hs x
  refine ⟨by rw [localizedFlow_P_abs_eq_rho X o h U P ρ hf hs.1];exact hρ.2,?_⟩
  calc
    |U x s|= -U x s := abs_of_nonpos (F02Aux.potential_nonpos X o h U P ρ hf hs.1 x)
    _ ≤ s*ρ x s := F02Aux.neg_potential_le_time_mul_rho X o h U P ρ hf hs.1 x
    _ ≤ T*ρ x T := mul_le_mul hs.2 hρ.2 hρ.1 (hs.1.trans hs.2)

end Yau.Proofs.F03Aux
