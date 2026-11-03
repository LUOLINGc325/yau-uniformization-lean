import Yau.Proofs.F05BootstrapHalfSpaceEstimate
import Yau.Proofs.F05BootstrapLocalizedEquation
import Yau.Proofs.F05BootstrapSourceBound

/-! The actual Hölder-only inverse estimates a localized relative solution
on its true half-space. The inverse constants precede every annulus, cutoff,
coefficient and unknown; no artificial boundary datum is supplied. -/

open Set Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1800000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_relative_halfSpace_patch_estimate {α M lam upper : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (e : Space n) (he : ‖e‖ = 1)
    {K : Set (Space n)} (hK : IsCompact K) (hKH : K ⊆ {x | 0 ≤ inner ℝ e x}) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧
      ∀ (T : ℝ) (a : Point n → Mat n) (b : Point n → RIdx n → ℝ)
        (f u : Point n → ℝ) (X V : Set (Space n)) (φ : Space n → ℝ) (θ : ℝ → ℝ)
        (F L E0 E1 E2 H0 H1 : ℝ),
      0 < T → T ≤ δ → UniqueDiffOn ℝ X → IsOpen V →
      ({x | 0 ≤ inner ℝ e x} ∩ V ⊆ X) →
      ContDiff ℝ 2 φ → tsupport φ ⊆ V → ContDiff ℝ 1 θ →
      θ =ᶠ[𝓝 0] (fun _ => 0) →
      HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) a M →
      (∀ j, HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) (fun z => b z j) M) →
      Elliptic (cylinder {x | 0 ≤ inner ℝ e x} 0 T) a lam upper →
      (∀ z ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T, z.1 ∉ K → a z = 1) →
      F05RelC2 X (Icc 0 T) u →
      (∀ x ∈ X, inner ℝ e x = 0 → ∀ t ∈ Icc 0 T, u (x,t) = 0) →
      (∀ z ∈ X ×ˢ Icc 0 T, F05RelOp X (Icc 0 T) a b u z = f z) →
      HolderBound α (({x | 0 ≤ inner ℝ e x} ∩ V) ×ˢ Icc 0 T)
        (fun z => (u z,F05RelD X u z)) L →
      HolderBound α (({x | 0 ≤ inner ℝ e x} ∩ V) ×ˢ Icc 0 T) f F →
      HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) (fun z => φ z.1) E0 →
      HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) (fun z => fderiv ℝ φ z.1) E1 →
      HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T)
        (fun z => fderiv ℝ (fderiv ℝ φ) z.1) E2 →
      HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) (fun z => θ z.2) H0 →
      HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) (fun z => deriv θ z.2) H1 →
      F05RelSchauder α {x | 0 ≤ inner ℝ e x} (Icc 0 T)
        (fun z => θ z.2*(φ z.1*u z))
        (C*(4*H0*E0*F+(2*H0*spatialCutoffCommutatorBudget n M E1 E2+4*H1*E0)*L)) := by
  obtain ⟨δ,C,hδ,hδ1,hC,hEstimate⟩ :=
    F05_relative_halfSpace_classical_estimate (M := M) (lam := lam) (upper := upper)
      hα hα1 e he hK hKH
  refine ⟨δ,C,hδ,hδ1,hC,?_⟩
  intro T a b f u X V φ θ F L E0 E1 E2 H0 H1 hT hTδ hX hV hVX hφ hSupport hθ hθZero
    ha hb hEll hExterior hu hFace hPDE hLow hf hφ0 hφD hφDD hθ0 hθD
  let g : Point n → ℝ := fun z => θ z.2*(φ z.1*f z-F05RelSpatialCommutator X a b φ u z)+
    deriv θ z.2*(φ z.1*u z)
  have hSource := F05_localized_relative_source_holder ha hb hφ0 hφD hφDD hSupport hLow hf hθ0 hθD
  obtain ⟨hW,hEq⟩ := F05_localized_relative_cutoff_equation (F05_halfSpace_uniqueDiffOn he)
    hX (uniqueDiffOn_Icc hT) hV hVX hφ hSupport hθ hu a b hPDE
  have hWBound : ∀ z ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T,
      |θ z.2*(φ z.1*u z)| ≤ H0*(E0*L) := by
    intro z hz
    by_cases hCut : φ z.1 = 0
    · simp only [hCut,zero_mul,mul_zero,abs_zero]
      exact mul_nonneg hθ0.1 (mul_nonneg hφ0.1 hLow.1)
    · have hzV : z.1 ∈ V := hSupport (subset_tsupport φ hCut)
      have hzSmall : z ∈ ({x | 0 ≤ inner ℝ e x} ∩ V) ×ˢ Icc 0 T := ⟨⟨hz.1,hzV⟩,hz.2⟩
      have hU : |u z| ≤ L := (holderBound_fst hLow).2.1 z hzSmall
      have hPhi : |φ z.1| ≤ E0 := hφ0.2.1 z hz
      have hTheta : |θ z.2| ≤ H0 := hθ0.2.1 z hz
      rw [abs_mul,abs_mul]
      exact mul_le_mul hTheta (mul_le_mul hPhi hU (abs_nonneg _) hφ0.1)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hθ0.1
  have hWFace : ∀ x, inner ℝ e x = 0 → ∀ t ∈ Icc 0 T, θ t*(φ x*u (x,t)) = 0 := by
    intro x hx t ht
    by_cases hCut : φ x = 0
    · rw [hCut,zero_mul,mul_zero]
    · have hxX := hVX ⟨hx.ge,hSupport (subset_tsupport φ hCut)⟩
      rw [hFace x hxX hx t ht,mul_zero,mul_zero]
  apply hEstimate T a b g (fun z => θ z.2*(φ z.1*u z)) _ (H0*(E0*L)) hT hTδ
    ha hb hEll hExterior hSource
    (fun x hx => F05_localized_relative_source_initial_zero X a b φ u f hθZero x)
    hW hWBound (fun x hx => F05_relative_localized_initial hθZero.self_of_nhds φ u x) hWFace
  intro z hz
  exact hEq z ⟨(show 0 < inner ℝ e z.1 from hz.1).le,hz.2.1.le,hz.2.2⟩

end Yau.Proofs.F05Aux
