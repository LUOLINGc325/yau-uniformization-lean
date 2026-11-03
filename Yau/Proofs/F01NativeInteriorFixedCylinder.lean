import Yau.Proofs.F01NativeSchauderEstimates
import Yau.Proofs.F01SchauderFixedCylinder

/-! The actual original L16 estimate gives one full Schauder bound
on a fixed closed inner cylinder, from the realized elliptic equation
and its proved coefficient/source bounds. No local estimate is assumed. -/
noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem native_interior_fixed_cylinder_budget (hn : 0 < n)
    {κ β ell upper M B F : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hβ : 0 < β) (hβ1 : β < 1) (hM : 0 < M) (hB : 0 ≤ B) (hF : 0 ≤ F) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Set (Space n)) (a b r l s : ℝ)
      (A : Point n → Mat n) (u f : Point n → ℝ),
      l < s → ball 0 r ⊆ S → Icc l s ⊆ Icc a b →
      (∀ c ∈ ball 0 r, ∀ τ ∈ Icc l s,
        MapsTo (fun x => κ • x + c) (ball 0 2) S ∧
        MapsTo (fun t => τ + κ ^ 2 * t) (Icc (-4) 0) (Icc a b)) →
      Elliptic (cylinder S a b) A ell upper →
      HolderBound β (cylinder S a b) A M →
      HolderBound β (cylinder S a b) f F → C2 (cylinder S a b) u →
      (∀ p ∈ cylinder S a b, |u p| ≤ B) →
      (∀ p ∈ cylinder S a b, linearOp (cylinder S a b) A (fun _ _ => 0) u p = f p) →
      SchauderBound β (cylinder (ball 0 r) l s) u C := by
  obtain ⟨Cp, hCp, hEstimate⟩ := interior_schauder_affine (n := n)
    (ell := ell) (upper := upper) hn hβ hβ1 hM
  have hBudget : 0 ≤ Cp * (B + F) := mul_nonneg hCp.le (add_nonneg hB hF)
  obtain ⟨C, hC, hFixed⟩ := schauder_fixed_cylinder_budget (n := n) hκ hβ.le hBudget
  refine ⟨C, hC, ?_⟩
  intro S a b r l s A u f hls hSpace hClock hMaps hEll hA hf hu hSup hEq
  apply hFixed S a b r l s u hls hSpace hClock hu
  · intro c hc τ hτ
    have hm := hMaps c hc τ hτ
    constructor
    · intro x hx
      exact hm.1 (Metric.ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2) hx)
    · intro t ht
      exact hm.2 ⟨by linarith [ht.1], ht.2⟩
  · intro c hc τ hτ
    have hm := hMaps c hc τ hτ
    exact hEstimate S a b κ τ c A u f F B (by simpa only [abs_of_pos hκ] using hκ1)
      hm.1 hm.2 hEll hA hf hu hSup hEq

end Yau.NodeProofs.F01Aux
