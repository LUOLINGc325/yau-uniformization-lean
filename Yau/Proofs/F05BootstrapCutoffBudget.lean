import Yau.LeafProofs.L16LocalCutoffBudgets

/-! Uniform numerical bounds for the actual spatial and temporal cutoffs.
The constants are chosen before the cutoff radius, center, and source budgets. -/

open Set
open scoped ContDiff
noncomputable section
set_option maxHeartbeats 1200000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_uniform_relative_cutoff_budget {α δ M : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hM : 0 ≤ M) :
    ∃ A : ℝ, 0 < A ∧ ∀ (h : ℝ) (hh : 0 < h), h ≤ 1 → ∀ c : Space n,
      ∃ E H : ℝ,
        HolderBound α (cylinder univ 0 (localSchauderTime δ h))
          (fun z => (innerPatchBump (h/8) (by positivity) c : Space n → ℝ) z.1) E ∧
        HolderBound α (cylinder univ 0 (localSchauderTime δ h))
          (fun z => fderiv ℝ (innerPatchBump (h/8) (by positivity) c : Space n → ℝ) z.1) E ∧
        HolderBound α (cylinder univ 0 (localSchauderTime δ h))
          (fun z => fderiv ℝ (fderiv ℝ (innerPatchBump (h/8) (by positivity) c : Space n → ℝ)) z.1) E ∧
        HolderBound α (cylinder (n := n) univ 0 (localSchauderTime δ h))
          (fun z => initialTimeCutoff (localSchauderTime δ h) z.2) H ∧
        HolderBound α (cylinder (n := n) univ 0 (localSchauderTime δ h))
          (fun z => deriv (initialTimeCutoff (localSchauderTime δ h)) z.2) H ∧
        ∀ F L : ℝ, 0 ≤ F → 0 ≤ L →
          4*H*E*F+(2*H*spatialCutoffCommutatorBudget n M E E+4*H*E)*L ≤
            A*(h⁻¹)^8*(F+L) := by
  obtain ⟨Cφ,hCφ,hCut⟩ := patchBumps_uniform_three_holderBounds (n := n) hα hα1
  obtain ⟨Cθ,hCθ,hTime⟩ := initialTimeCutoff_uniform_holder_jets (n := n) hα hα1
  let k : ℝ := 12*(Fintype.card (Yau.RIdx n) : ℝ)^2+4*(Fintype.card (Yau.RIdx n) : ℝ)
  let Cbase : ℝ := 65536*Cθ*Cφ*(δ⁻¹)^2
  let A : ℝ := Cbase*(2*k*M+8)
  have hk : 0 ≤ k := by dsimp only [k]; positivity
  have hBase : 0 < Cbase := by dsimp only [Cbase]; positivity
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨A,hA,?_⟩
  intro h hh hh1 c
  let T : ℝ := localSchauderTime δ h
  let rb : ℝ := h/8
  have hrb : 0 < rb := by dsimp only [rb]; positivity
  have hrb1 : rb ≤ 1 := by dsimp only [rb]; linarith
  let φ : Space n → ℝ := innerPatchBump rb hrb c
  have hT : 0 < T := by dsimp only [T,localSchauderTime]; positivity
  have hTδ : T ≤ δ := by
    have hBoundH : h^2/8 ≤ 1 := by nlinarith
    calc
      T = δ*(h^2/8) := by dsimp only [T,localSchauderTime]; ring
      _ ≤ δ*1 := mul_le_mul_of_nonneg_left hBoundH hδ.le
      _ = δ := mul_one _
  have hT1 : T ≤ 1 := hTδ.trans hδ1
  let E : ℝ := 2*Cφ*(rb⁻¹)^3
  let H : ℝ := Cθ/T^2
  have hInv : 1 ≤ rb⁻¹ := (one_le_inv₀ hrb).mpr hrb1
  have hPow : rb^(1-α) ≤ 1 := Real.rpow_le_one hrb.le hrb1 (by linarith)
  have hBudget (j : ℕ) (hj : j ≤ 3) :
      2*((rb⁻¹)^j*Cφ)*rb^(1-α) ≤ E := by
    calc
      _ ≤ 2*((rb⁻¹)^j*Cφ)*1 := mul_le_mul_of_nonneg_left hPow (by positivity)
      _ ≤ E := by
        dsimp only [E]
        have hMono := pow_le_pow_right₀ hInv hj
        nlinarith [mul_le_mul_of_nonneg_right hMono hCφ.le]
  have hRaw := hCut rb hrb hrb1 T c φ (Or.inl rfl)
  have hφ0 := holderBound_mono_const hRaw.1 (show 2*(rb⁻¹*Cφ)*rb^(1-α) ≤ E by
    simpa only [pow_one] using hBudget 1 (by norm_num))
  have hφ1 := holderBound_mono_const hRaw.2.1 (hBudget 2 (by norm_num))
  have hφ2 := holderBound_mono_const hRaw.2.2 (hBudget 3 le_rfl)
  have hΘ := hTime T hT hT1
  refine ⟨E,H,hφ0,hφ1,hφ2,hΘ.1,hΘ.2,?_⟩
  intro F L hF hL
  have hComm : spatialCutoffCommutatorBudget n M E E = k*M*E := by
    dsimp only [spatialCutoffCommutatorBudget,k]
    ring
  have hHE : H*E = Cbase*(h⁻¹)^7 := by
    dsimp only [H,E,Cbase,rb,T,localSchauderTime]
    field_simp
    ring
  have hRawEq :
      4*H*E*F+(2*H*spatialCutoffCommutatorBudget n M E E+4*H*E)*L =
        Cbase*(h⁻¹)^7*(4*F+(2*k*M+4)*L) := by
    rw [hComm,← hHE]
    ring
  rw [hRawEq]
  have hCoeff : 4*F+(2*k*M+4)*L ≤ (2*k*M+8)*(F+L) := by
    have hNonneg : 0 ≤ (2*k*M+4)*F := by positivity
    nlinarith
  have hhInv : 1 ≤ h⁻¹ := (one_le_inv₀ hh).mpr hh1
  have h78 : (h⁻¹)^7 ≤ (h⁻¹)^8 := pow_le_pow_right₀ hhInv (by norm_num)
  calc
    _ ≤ Cbase*(h⁻¹)^7*((2*k*M+8)*(F+L)) :=
      mul_le_mul_of_nonneg_left hCoeff (by positivity)
    _ = A*(h⁻¹)^7*(F+L) := by dsimp only [A]; ring
    _ ≤ A*(h⁻¹)^8*(F+L) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h78 hA.le) (by positivity)

end Yau.Proofs.F05Aux
