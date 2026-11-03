import Yau.LeafProofs.L16InitialTimeCutoff

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

def localSchauderTime (δ h : ℝ) : ℝ := δ*h^2/8

/-- The actual compact space-time localization source has a fixed power
    budget, uniform in the center, coefficients, and classical solution. -/
theorem exists_uniform_localized_classical_source_budget {n : ℕ} {α δ M : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hM : 0 ≤ M) :
    ∃ A : ℝ, 0 < A ∧ ∀ (h : ℝ) (hh : 0 < h), h ≤ 1 →
      ∀ (c : Space n) (O : Set (Space n)) (a : Point n → Mat n)
        (b : Point n → Yau.RIdx n → ℝ) (f u : Point n → ℝ) (F L : ℝ),
      let T := localSchauderTime δ h
      let φ : Space n → ℝ := innerPatchBump (h/8) (by positivity) c
      HolderBound α (cylinder Set.univ 0 T) a M →
      (∀ i, HolderBound α (cylinder Set.univ 0 T) (fun p => b p i) M) →
      tsupport φ ⊆ O →
      HolderBound α (cylinder O 0 T) (fun p => (u p,spatialD u p)) L →
      HolderBound α (cylinder O 0 T) f F →
      HolderBound α (cylinder Set.univ 0 T)
        (fun p => initialTimeCutoff T p.2*(φ p.1*f p-spatialCutoffCommutator a b φ u p)+
          deriv (initialTimeCutoff T) p.2*(φ p.1*u p))
        (A*(h⁻¹)^8*(F+L)) := by
  obtain ⟨Cφ,hCφ,hCut⟩ := patchBumps_uniform_three_holderBounds (n := n) hα hα1
  obtain ⟨Cθ,hCθ,hTime⟩ := initialTimeCutoff_uniform_holder_jets (n := n) hα hα1
  let k : ℝ := 12*(Fintype.card (Yau.RIdx n) : ℝ)^2+4*(Fintype.card (Yau.RIdx n) : ℝ)
  let Cbase : ℝ := 65536*Cθ*Cφ*(δ⁻¹)^2
  let A : ℝ := Cbase*(2*k*M+8)
  have hk : 0 ≤ k := by dsimp only [k]; positivity
  have hBase : 0 < Cbase := by dsimp only [Cbase]; positivity
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨A,hA,?_⟩
  intro h hh hh1 c O a b f u F L
  dsimp only
  let T : ℝ := localSchauderTime δ h
  let rb : ℝ := h/8
  have hrb : 0 < rb := by dsimp only [rb]; positivity
  have hrb1 : rb ≤ 1 := by dsimp only [rb]; linarith
  let φ : Space n → ℝ := innerPatchBump rb hrb c
  intro ha hb hSupport hLow hf
  have hF : 0 ≤ F := hf.1
  have hL : 0 ≤ L := hLow.1
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
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hInv : 1 ≤ rb⁻¹ := (one_le_inv₀ hrb).mpr hrb1
  have hPow : rb^(1-α) ≤ 1 := Real.rpow_le_one hrb.le hrb1 (by linarith)
  have hBudget (j : ℕ) (hj : j ≤ 3) :
      2*((rb⁻¹)^j*Cφ)*rb^(1-α) ≤ E := by
    calc
      _ ≤ 2*((rb⁻¹)^j*Cφ)*1 :=
        mul_le_mul_of_nonneg_left hPow (by positivity)
      _ ≤ E := by
        dsimp only [E]
        have hMono := pow_le_pow_right₀ hInv hj
        nlinarith [mul_le_mul_of_nonneg_right hMono hCφ.le]
  have hRaw := hCut rb hrb hrb1 T c φ (Or.inl rfl)
  have hφ0 : HolderBound α (cylinder Set.univ 0 T) (fun p => φ p.1) E := by
    apply holderBound_mono_const hRaw.1
    simpa only [pow_one] using hBudget 1 (by norm_num)
  have hφ1 : HolderBound α (cylinder Set.univ 0 T) (fun p => fderiv ℝ φ p.1) E :=
    holderBound_mono_const hRaw.2.1 (hBudget 2 (by norm_num))
  have hφ2 : HolderBound α (cylinder Set.univ 0 T)
      (fun p => fderiv ℝ (fderiv ℝ φ) p.1) E :=
    holderBound_mono_const hRaw.2.2 (hBudget 3 le_rfl)
  have hΘ := hTime T hT hT1
  have hActual := localized_classical_source_holderBound ha hb hφ0 hφ1 hφ2 hSupport hLow hf
    hΘ.1 hΘ.2
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
  apply holderBound_mono_const hActual
  change 4*H*E*F+(2*H*spatialCutoffCommutatorBudget n M E E+4*H*E)*L ≤ _
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

end Yau.LeafProofs.L16Aux
