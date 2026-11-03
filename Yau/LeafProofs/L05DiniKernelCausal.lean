import Yau.LeafProofs.L05DiniKernelTransport
import Yau.LeafProofs.L05DiniKernelRepresentation

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic
open L16Aux

local instance l05DiniKernelCausalDualGroup (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance l05DiniKernelCausalDualSpace (n : ℕ) : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance l05DiniKernelCausalHessianGroup (n : ℕ) : NormedAddCommGroup (DiniHessian n) := inferInstance
local instance l05DiniKernelCausalHessianSpace (n : ℕ) : NormedSpace ℝ (DiniHessian n) := inferInstance

theorem constant_causal_dini_hessian (n : ℕ) (_hn : 0 < n) (ell L : ℝ)
    (hell : 0 < ell) (hL : ell ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : Mat n) (T eta G F B W : ℝ)
      (g w : Point n → ℝ) (phi : ℝ → ℝ),
      0 < T → T ≤ 1 → 0 < eta → eta < 1 → 0 ≤ G → 0 ≤ F → 0 ≤ B → 0 ≤ W →
      Elliptic (cylinder Set.univ 0 T) (fun _ => A) ell L →
      HolderBound eta (cylinder Set.univ 0 T) g F →
      (∀ p ∈ cylinder Set.univ 0 T, |g p| ≤ G) → (∀ x : Space n, g (x,0)=0) →
      Measurable phi → MonotoneOn phi (Set.Ioc (0:ℝ) 1) → powerBound eta B phi →
      (∀ r ∈ Set.Ioc (0:ℝ) 1, ∀ p ∈ cylinder Set.univ 0 T, ∀ q ∈ cylinder Set.univ 0 T,
        parabolicDistance p q ≤ r → |g p-g q| ≤ phi r) →
      C2 (cylinder Set.univ 0 T) w → (∀ p ∈ cylinder Set.univ 0 T, |w p| ≤ W) →
      (∀ x : Space n, w (x,0)=0) →
      (∀ p ∈ Set.univ ×ˢ Set.Ioc (0:ℝ) T,
        linearOp (cylinder Set.univ 0 T) (fun _ => A) (fun _ _ => 0) w p=g p) →
      ∀ r ∈ Set.Ioc (0:ℝ) 1, ∀ p ∈ cylinder Set.univ 0 T, ∀ q ∈ cylinder Set.univ 0 T,
        parabolicDistance p q ≤ r → ‖spatialDD w p-spatialDD w q‖ ≤ C*(diniTransform phi r+r*G) := by
  let b : ℝ := 1+(Real.sqrt ell)⁻¹
  let c : ℝ := 1+Real.sqrt L
  have hb : 1 ≤ b := le_add_of_nonneg_right (inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hc : 1 ≤ c := le_add_of_nonneg_right (Real.sqrt_nonneg _)
  obtain ⟨C,hC,hPotential⟩ := constantHeatDuhamel_dini_hessian (n := n) b c hb hc
  refine ⟨C,hC,?_⟩
  intro A T eta G F B W g w phi hT hT1 he he1 hG0 hF hB hW hEll hg hG hg0 hm hmono hp hmod hw hwB hw0 hPDE
  have hOrigin : ((0 : Space n),(0:ℝ)) ∈ cylinder Set.univ 0 T := ⟨Set.mem_univ _,le_rfl,hT.le⟩
  have hA := hEll.2.2 (0,0) hOrigin
  obtain ⟨S,hS,hSinv,hTrace⟩ := elliptic_matrix_space_equiv A hell hL hA.1 hA.2
  have hSc : ‖(S : Space n →L[ℝ] Space n)‖ ≤ c :=
    hS.trans (le_add_of_nonneg_left zero_le_one)
  have hSb : ‖(S.symm : Space n →L[ℝ] Space n)‖ ≤ b :=
    hSinv.trans (le_add_of_nonneg_left zero_le_one)
  have hEq := constant_causal_representation S hTrace hT hT1 he he1 hEll hg hw hwB hw0 hPDE
  intro r hr p hpm q hqm hpq
  rw [spatialDD_congr_cylinder_univ hEq hpm,spatialDD_congr_cylinder_univ hEq hqm]
  exact hPotential S hSc hSb T eta G F B g phi hT hT1 he he1 hG0 hF hB hg hG hm hmono hp hmod r hr p hpm q hqm hpq

end Yau.LeafProofs.L05Aux
