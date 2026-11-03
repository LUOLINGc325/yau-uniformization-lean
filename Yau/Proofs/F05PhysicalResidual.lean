import Yau.Proofs.F05PhysicalFactories
import Yau.Proofs.F05OuterResidual
import Yau.Proofs.F05CoefficientExtension

/-! The native patch equation determines a linear physical residual. The
outer cutoff keeps both that residual and its actual commutator. -/

open Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_patch_residual_add {O : Set (Space n)} {α T : ℝ}
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ) (ψ : Space n → ℝ)
    (W H : compatibleHolderGraph α O T → Point n → ℝ)
    (hW : ∀ f, C2 (cylinder univ 0 T) (W f))
    (hAdd : ∀ f g p, p ∈ cylinder univ 0 T → W (f+g) p = W f p+W g p)
    (hEq : ∀ f p, p ∈ cylinder (closure O) 0 T →
      linearOp (cylinder (closure O) 0 T) a b (W f) p =
        ψ p.1*compatibleHolderFun f p-H f p)
    (f g : compatibleHolderGraph α O T) {p : Point n}
    (hp : p ∈ cylinder (closure O) 0 T) : H (f+g) p = H f p+H g p := by
  have hpA : p ∈ cylinder univ 0 T := ⟨mem_univ _,hp.2⟩
  have hOp : linearOp (cylinder (closure O) 0 T) a b (W (f+g)) p =
      linearOp (cylinder (closure O) 0 T) a b (W f) p+
        linearOp (cylinder (closure O) 0 T) a b (W g) p := by
    simp only [linearOp_cylinder_restrict_space a b _ hp]
    rw [linearOp_congr_cylinder_univ (hAdd f g) a b hpA,
      linearOp_add (hW f) (hW g) hpA]
  rw [hEq (f+g) p hp,hEq f p hp,hEq g p hp,compatibleHolderFun_add] at hOp
  simp only [Pi.add_apply] at hOp
  linarith

theorem F05_patch_residual_smul {O : Set (Space n)} {α T : ℝ}
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ) (ψ : Space n → ℝ)
    (W H : compatibleHolderGraph α O T → Point n → ℝ)
    (hW : ∀ f, C2 (cylinder univ 0 T) (W f))
    (hSmul : ∀ (d : ℝ) f p, p ∈ cylinder univ 0 T → W (d • f) p = d*W f p)
    (hEq : ∀ f p, p ∈ cylinder (closure O) 0 T →
      linearOp (cylinder (closure O) 0 T) a b (W f) p =
        ψ p.1*compatibleHolderFun f p-H f p)
    (d : ℝ) (f : compatibleHolderGraph α O T) {p : Point n}
    (hp : p ∈ cylinder (closure O) 0 T) : H (d • f) p = d*H f p := by
  have hpA : p ∈ cylinder univ 0 T := ⟨mem_univ _,hp.2⟩
  have hOp : linearOp (cylinder (closure O) 0 T) a b (W (d • f)) p =
      d*linearOp (cylinder (closure O) 0 T) a b (W f) p := by
    simp only [linearOp_cylinder_restrict_space a b _ hp]
    rw [linearOp_congr_cylinder_univ (hSmul d f) a b hpA]
    have hScalar := linearOp_const_smul (a := a) (b := b) (hW f) d hpA
    have hFn : (d • W f) = (fun q => d*W f q) := by funext q; rfl
    rw [hFn] at hScalar
    exact hScalar
  rw [hEq (d • f) p hp,hEq f p hp,compatibleHolderFun_smul] at hOp
  simp only [Pi.smul_apply,smul_eq_mul] at hOp
  nlinarith only [hOp]

theorem F05_outer_patch_equation {Q : Set (Point n)}
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ)
    (β ψ : Space n → ℝ) (W f H : Point n → ℝ) {p : Point n}
    (hβ : ContDiffAt ℝ 2 β p.1)
    (hW : ContDiffAt ℝ 2 (fun z => W (z,p.2)) p.1)
    (hEq : linearOp Q a b W p = ψ p.1*f p-H p)
    (hPlateau : β p.1*ψ p.1 = ψ p.1) :
    linearOp Q a b (fun q => β q.1*W q) p =
      ψ p.1*f p-F05OuterResidual a b β W H p := by
  rw [linearOp_spatial_mul hβ hW,hEq]
  unfold F05OuterResidual spatialCutoffCommutator
  linear_combination hPlateau*f p

theorem F05_cutoff_operator_extension_exact (Q : Set (Point n))
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ)
    (β : Space n → ℝ) (W : Point n → ℝ)
    (hSupport : tsupport β ⊆ Metric.closedBall 0 1) (p : Point n) :
    linearOp Q (F05PrincipalExtension a) (F05DriftExtension b) (fun q => β q.1*W q) p =
      linearOp Q a b (fun q => β q.1*W q) p := by
  by_cases hp : ‖p.1‖ ≤ 1
  · have hExact := F05_coefficient_extension_exact (a := a) (b := b) hp
    simp only [linearOp,hExact.1,hExact.2]
  · have hOut : p.1 ∉ tsupport β := by
      intro hMem
      exact hp (by simpa only [Metric.mem_closedBall,dist_zero_right] using hSupport hMem)
    have hZero := spatial_cutoff_jets_zero_of_notMem_tsupport Q β W hOut
    simp only [linearOp,hZero.2.1,hZero.2.2.1,ContinuousLinearMap.zero_apply,
      mul_zero,Finset.sum_const_zero,sub_zero]

theorem F05_outer_original_patch_equation {Q : Set (Point n)}
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ)
    (β ψ : Space n → ℝ) (W f H : Point n → ℝ) {p : Point n}
    (hSupport : tsupport β ⊆ Metric.closedBall 0 1)
    (hβ : ContDiffAt ℝ 2 β p.1)
    (hW : ContDiffAt ℝ 2 (fun z => W (z,p.2)) p.1)
    (hEq : linearOp Q (F05PrincipalExtension a) (F05DriftExtension b) W p =
      ψ p.1*f p-H p) (hPlateau : β p.1*ψ p.1 = ψ p.1) :
    linearOp Q a b (fun q => β q.1*W q) p = ψ p.1*f p-
      F05OuterResidual (F05PrincipalExtension a) (F05DriftExtension b) β W H p := by
  rw [← F05_cutoff_operator_extension_exact Q a b β W hSupport p]
  exact F05_outer_patch_equation _ _ β ψ W f H hβ hW hEq hPlateau

end Yau.Proofs.F05Aux
