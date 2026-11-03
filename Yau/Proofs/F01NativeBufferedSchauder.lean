import Yau.Proofs.F01NativeInteriorFixedCylinder
import Yau.Proofs.F01BufferedParabolicPatches

/-! The original interior estimate on two concentric buffered spatial
balls, with the original closed time slab. All geometric buffers are
checked as actual affine maps into the outer cylinder. -/
noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem native_buffered_linear_schauder_budget (hn : 0 < n)
    {κ β ell upper M B F : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hβ : 0 < β) (hβ1 : β < 1) (hM : 0 < M) (hB : 0 ≤ B) (hF : 0 ≤ F) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R r a b l s : ℝ)
      (A : Point n → Mat n) (u f : Point n → ℝ),
      l < s → r + 2 * κ ≤ R → a + 4 * κ ^ 2 ≤ l → s ≤ b →
      Elliptic (cylinder (ball 0 R) a b) A ell upper →
      HolderBound β (cylinder (ball 0 R) a b) A M →
      HolderBound β (cylinder (ball 0 R) a b) f F → C2 (cylinder (ball 0 R) a b) u →
      (∀ p ∈ cylinder (ball 0 R) a b, |u p| ≤ B) →
      (∀ p ∈ cylinder (ball 0 R) a b,
        linearOp (cylinder (ball 0 R) a b) A (fun _ _ => 0) u p = f p) →
      SchauderBound β (cylinder (ball 0 r) l s) u C := by
  obtain ⟨C, hC, hc⟩ := native_interior_fixed_cylinder_budget (n := n)
    (ell := ell) (upper := upper) hn hκ hκ1 hβ hβ1 hM hB hF
  refine ⟨C, hC, ?_⟩
  intro R r a b l s A u f hls hSpace hLower hUpper hEll hA hf hu hSup hEq
  apply hc (ball 0 R) a b r l s A u f hls
  · exact Metric.ball_subset_ball (by linarith)
  · intro t ht
    exact ⟨by nlinarith [ht.1, sq_nonneg κ], ht.2.trans hUpper⟩
  · intro c hc τ hτ
    exact buffered_backward_patch_maps hκ hc hτ hSpace hLower hUpper
  · exact hEll
  · exact hA
  · exact hf
  · exact hu
  · exact hSup
  · exact hEq

end Yau.NodeProofs.F01Aux
