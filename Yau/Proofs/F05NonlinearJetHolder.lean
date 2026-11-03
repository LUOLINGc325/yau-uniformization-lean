import Yau.Proofs.F05NonlinearChart
import Yau.Proofs.F05CanonicalAlgebra
import Yau.Proofs.F05CanonicalSmallHolder

/-! The true original nonlinear source is Lipschitz with a small factor on
fixed balls in the actual complete compatible-jet norm. -/

open Set
noncomputable section
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_nonlinear_jet_holder {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (h : ℝ → HermitianField M) {S : ℝ} (hS : 0 < S) (hh : MetricFamilySmooth h (Icc 0 S))
    {α B r : ℝ} (hα : 0 < α) (hα1 : α < 1) (hB : 0 < B) (hr : 0 < r) :
    ∃ G C : ℝ, 0 < G ∧ 0 < C ∧ ∀ (ρ T : ℝ) (hT : 0 < T),
      0 < ρ → ρ ≤ 1 → T ≤ ρ^2 → T ≤ S → G*ρ^(1-α) ≤ 1 →
      ∀ p : M.Carrier → ℝ → ℝ,
      (∀ i, C2 (F05Q A i T) (pull A i p)) →
      (∀ i, HolderBound α (F05Q A i T) (pull A i (fun x t => Real.exp (-p x t))) B) →
      (∀ i, HolderBound α (F05Q A i T) (pull A i (fun x t => laplacian (h t) (fun y => p y t) x)) B) →
      (∀ i, HolderBound α (F05Q A i T) (pull A i (fun x t => scalarCurvature (h t) x)) B) →
      ∀ u v : F05CompatibleJetGraph A α hT.le, ‖u‖ ≤ r → ‖v‖ ≤ r → ∀ i : Fin A.count,
      HolderBound α (F05Q A i T)
        (fun q => pull A i (F05NonlinearCorrection h T p (F05CanonicalJetFunction A χ α hT.le u)) q-
          pull A i (F05NonlinearCorrection h T p (F05CanonicalJetFunction A χ α hT.le v)) q)
        (C*ρ^(1-α)*‖u-v‖) := by
  obtain ⟨G,hG,hLow⟩ := F05_canonical_small_lower_holder hA hχ hα hα1
  obtain ⟨K,hK,hLap⟩ := F05_jet_laplacian_holder_uniform hA hχ h hS hh hα hα1
  obtain ⟨C,hC,hScalar⟩ := F05_scalar_correction_lipschitz (n := n) B K r hB hK hr
  refine ⟨G,C*G,hG,mul_pos hC hG,?_⟩
  intro ρ T hT hρ hρ1 hTρ hTS hSmall p hP ha hb hR u v hu hv i
  have hPower : 0 ≤ ρ^(1-α) := Real.rpow_nonneg hρ.le _
  have hT1 : T ≤ 1 := by nlinarith [mul_nonneg hρ.le (sub_nonneg.mpr hρ1)]
  let s := G*ρ^(1-α)
  have hs : 0 ≤ s := mul_nonneg hG.le hPower
  have hLowU (w : F05CompatibleJetGraph A α hT.le) (hw : ‖w‖ ≤ r) :
      HolderBound α (F05Q A i T) (F05CanonicalPull A χ α hT.le w i) (s*r) := by
    apply holderBound_mono_const (holderBound_fst (hLow ρ T hT hρ hρ1 hTρ w i))
    calc
      G*‖w‖*ρ^(1-α) ≤ G*r*ρ^(1-α) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hw hG.le) hPower
      _ = s*r := by dsimp only [s]; ring
  have hLowDiff : HolderBound α (F05Q A i T)
      (fun q => F05CanonicalPull A χ α hT.le u i q-F05CanonicalPull A χ α hT.le v i q) (s*‖u-v‖) := by
    have hh := holderBound_fst (hLow ρ T hT hρ hρ1 hTρ (u-v) i)
    rw [F05CanonicalPull_sub] at hh
    convert hh using 1
    dsimp only [s]
    ring
  have hLapBall (w : F05CompatibleJetGraph A α hT.le) (hw : ‖w‖ ≤ r) :
      HolderBound α (F05Q A i T) (F05JetLaplacian A h α hT.le w i) (K*r) :=
    holderBound_mono_const (hLap T hT hTS hT1 w i) (mul_le_mul_of_nonneg_left hw hK.le)
  have hLapDiff : HolderBound α (F05Q A i T)
      (fun q => F05JetLaplacian A h α hT.le u i q-F05JetLaplacian A h α hT.le v i q) (K*‖u-v‖) :=
    holderBound_congr_on (hLap T hT hTS hT1 (u-v) i)
      (fun q hq => F05JetLaplacian_sub A h α hT.le u v i ⟨q,hq⟩)
  have hBound := hScalar α s ‖u-v‖ (F05Q A i T)
    (pull A i (fun x t => Real.exp (-p x t)))
    (pull A i (fun x t => laplacian (h t) (fun y => p y t) x))
    (pull A i (fun x t => scalarCurvature (h t) x))
    (pull A i (F05IntrinsicLinearOperator (fun x t => Real.exp (-p x t)) h T p))
    (F05CanonicalPull A χ α hT.le u i) (F05CanonicalPull A χ α hT.le v i)
    (F05JetLaplacian A h α hT.le u i) (F05JetLaplacian A h α hT.le v i)
    hs hSmall (norm_nonneg _) (ha i) (hb i) (hR i) (hLowU u hu) (hLowU v hv) hLowDiff
    (hLapBall u hu) (hLapBall v hv) hLapDiff
  have hActual := holderBound_congr_on hBound (fun q hq =>
    congrArg₂ (fun a b : ℝ => a-b)
      (F05_nonlinear_correction_eq_chart hA hχ h p α hT hP u i hq).symm
      (F05_nonlinear_correction_eq_chart hA hχ h p α hT hP v i hq).symm)
  convert hActual using 1
  dsimp only [s]
  ring

end Yau.Proofs.F05Aux
