import Yau.Proofs.P04PoleGlobalLevi

noncomputable section
open Set
open scoped Topology Manifold ContDiff Matrix ComplexOrder

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

theorem smooth_levi_add {f g : M.Carrier → ℝ} (hf : SmoothFn f) (hg : SmoothFn g)
    (x : M.Carrier) : levi (fun y => f y+g y) x=levi f x+levi g x := by
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hfn := ((hf x).contDiffAt ((isOpen_extChartAt_target x).mem_nhds hz)).of_le (by simp : (2 : ℕ∞ω) ≤ ∞)
  have hgn := ((hg x).contDiffAt ((isOpen_extChartAt_target x).mem_nhds hz)).of_le (by simp : (2 : ℕ∞ω) ≤ ∞)
  exact L17Aux.leviC_add hfn hgn

theorem smooth_levi_const_mul {f : M.Carrier → ℝ} (hf : SmoothFn f) (c : ℝ)
    (x : M.Carrier) : levi (fun y => c*f y) x=(c : ℂ) • levi f x := by
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hfn := ((hf x).contDiffAt ((isOpen_extChartAt_target x).mem_nhds hz)).of_le (by simp : (2 : ℕ∞ω) ≤ ∞)
  exact L17Aux.leviC_const_mul hfn c

theorem pole_weight_levi_sub_background (p : M.Carrier) {χ : ComplexVector n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hs : tsupport χ ⊆ chartTarget p)
    (c k : ℝ) {ψ : M.Carrier → ℝ} (hψ : SmoothFn ψ) {ε : ℝ} (hε : 0 < ε)
    (x : M.Carrier) :
    levi (regularizedPoleWeight p χ c k ψ ε) x-levi ψ x =
      levi (fun y => (k-1)*ψ y+globalPolePart p χ c ε y) x := by
  have hP := globalPolePart_smooth p hχ hcχ hs c hε
  have hF : SmoothFn (fun y => (k-1)*ψ y+globalPolePart p χ c ε y) :=
    fun a => (contDiffOn_const.mul (hψ a)).add (hP a)
  have heq : regularizedPoleWeight p χ c k ψ ε=
      (fun y => ((k-1)*ψ y+globalPolePart p χ c ε y)+ψ y) := by
    funext y
    unfold regularizedPoleWeight
    ring
  rw [heq,smooth_levi_add hF hψ,add_sub_cancel_right]

end Yau.Proofs.P04Aux
