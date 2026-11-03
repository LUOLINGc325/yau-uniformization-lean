import Yau.Proofs.F05BootstrapWholeSpace
import Yau.Proofs.F05BootstrapLocalizedEquation
import Yau.Proofs.F05BootstrapSourceBound

/-! The whole-space counterpart of the physical patch estimate. The native
constants are fixed before every artificial annulus and cutoff. -/

open Set Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1800000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_relative_wholeSpace_patch_estimate {α M lam upper : ℝ}
    (hα : 0 < α) (hα1 : α < 1) {K : Set (Space n)} (hK : IsCompact K) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧
      ∀ (T : ℝ) (a : Point n → Mat n) (b : Point n → RIdx n → ℝ)
        (f u : Point n → ℝ) (X V : Set (Space n)) (φ : Space n → ℝ) (θ : ℝ → ℝ)
        (F L E0 E1 E2 H0 H1 : ℝ),
      0 < T → T ≤ δ → UniqueDiffOn ℝ X → IsOpen V → V ⊆ X →
      ContDiff ℝ 2 φ → tsupport φ ⊆ V → ContDiff ℝ 1 θ →
      θ =ᶠ[𝓝 0] (fun _ => 0) →
      HolderBound α (cylinder (n := n) univ 0 T) a M →
      (∀ j, HolderBound α (cylinder (n := n) univ 0 T) (fun z => b z j) M) →
      Elliptic (cylinder (n := n) univ 0 T) a lam upper →
      (∀ z ∈ cylinder (n := n) univ 0 T, z.1 ∉ K → a z = 1) →
      F05RelC2 X (Icc 0 T) u →
      (∀ z ∈ X ×ˢ Icc 0 T, F05RelOp X (Icc 0 T) a b u z = f z) →
      HolderBound α (V ×ˢ Icc 0 T) (fun z => (u z,F05RelD X u z)) L →
      HolderBound α (V ×ˢ Icc 0 T) f F →
      HolderBound α (cylinder (n := n) univ 0 T) (fun z => φ z.1) E0 →
      HolderBound α (cylinder (n := n) univ 0 T) (fun z => fderiv ℝ φ z.1) E1 →
      HolderBound α (cylinder (n := n) univ 0 T) (fun z => fderiv ℝ (fderiv ℝ φ) z.1) E2 →
      HolderBound α (cylinder (n := n) univ 0 T) (fun z => θ z.2) H0 →
      HolderBound α (cylinder (n := n) univ 0 T) (fun z => deriv θ z.2) H1 →
      F05RelSchauder α univ (Icc 0 T) (fun z => θ z.2*(φ z.1*u z))
        (C*(4*H0*E0*F+(2*H0*spatialCutoffCommutatorBudget n M E1 E2+4*H1*E0)*L)) := by
  obtain ⟨δ,C,hδ,hδ1,hC,hEstimate⟩ :=
    F05_relative_wholeSpace_classical_estimate (M := M) (lam := lam) (upper := upper) hα hα1 hK
  refine ⟨δ,C,hδ,hδ1,hC,?_⟩
  intro T a b f u X V φ θ F L E0 E1 E2 H0 H1 hT hTδ hX hV hVX hφ hSupport hθ hθZero
    ha hb hEll hExterior hu hPDE hLow hf hφ0 hφD hφDD hθ0 hθD
  let g : Point n → ℝ := fun z => θ z.2*(φ z.1*f z-F05RelSpatialCommutator X a b φ u z)+
    deriv θ z.2*(φ z.1*u z)
  have hLow' : HolderBound α ((univ ∩ V) ×ˢ Icc 0 T) (fun z => (u z,F05RelD X u z)) L := by
    simpa only [univ_inter] using hLow
  have hf' : HolderBound α ((univ ∩ V) ×ˢ Icc 0 T) f F := by simpa only [univ_inter] using hf
  have hSource := F05_localized_relative_source_holder ha hb hφ0 hφD hφDD hSupport hLow' hf' hθ0 hθD
  obtain ⟨hW,hEq⟩ := F05_localized_relative_cutoff_equation uniqueDiffOn_univ hX
    (uniqueDiffOn_Icc hT) hV (fun x hx => hVX hx.2) hφ hSupport hθ hu a b hPDE
  have hWBound : ∀ z ∈ cylinder (n := n) univ 0 T, |θ z.2*(φ z.1*u z)| ≤ H0*(E0*L) := by
    intro z hz
    by_cases hCut : φ z.1 = 0
    · simp only [hCut,zero_mul,mul_zero,abs_zero]
      exact mul_nonneg hθ0.1 (mul_nonneg hφ0.1 hLow.1)
    · have hzV : z.1 ∈ V := hSupport (subset_tsupport φ hCut)
      have hU : |u z| ≤ L := (holderBound_fst hLow).2.1 z ⟨hzV,hz.2⟩
      have hPhi : |φ z.1| ≤ E0 := hφ0.2.1 z hz
      have hTheta : |θ z.2| ≤ H0 := hθ0.2.1 z hz
      rw [abs_mul,abs_mul]
      exact mul_le_mul hTheta (mul_le_mul hPhi hU (abs_nonneg _) hφ0.1)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hθ0.1
  exact hEstimate T a b g (fun z => θ z.2*(φ z.1*u z)) _ (H0*(E0*L)) hT hTδ
    ha hb hEll hExterior hSource hW hWBound
    (fun x => F05_relative_localized_initial hθZero.self_of_nhds φ u x) hEq

end Yau.Proofs.F05Aux
