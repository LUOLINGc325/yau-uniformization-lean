import Yau.LeafProofs.L05DiniKernelTemporal

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic
open L16Aux

local instance l05DiniKernelGlobalDualGroup (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance l05DiniKernelGlobalDualSpace (n : ℕ) : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance l05DiniKernelGlobalHessianGroup (n : ℕ) : NormedAddCommGroup (DiniHessian n) := inferInstance
local instance l05DiniKernelGlobalHessianSpace (n : ℕ) : NormedSpace ℝ (DiniHessian n) := inferInstance

theorem heatDuhamel_global_dini_hessian {n : ℕ} :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T eta G F B : ℝ) (g : Point n → ℝ) (psi : ℝ → ℝ),
      0 < T → T ≤ 1 → 0 < eta → eta < 1 → 0 ≤ G → 0 ≤ F → 0 ≤ B →
      HolderBound eta (cylinder Set.univ 0 T) g F →
      (∀ p ∈ cylinder Set.univ 0 T, |g p| ≤ G) →
      Measurable psi → psi 0=0 → MonotoneOn psi (Set.Ioi (0:ℝ)) →
      (∀ s : ℝ, 0 < s → 0 ≤ psi s ∧ psi s ≤ B*s^eta) →
      (∀ t ∈ Set.Icc (0:ℝ) T, ∀ x y : Space n, |g (x,t)-g (y,t)| ≤ psi ‖x-y‖) →
      ∀ r : ℝ, 0 < r → ∀ p ∈ cylinder Set.univ 0 T, ∀ q ∈ cylinder Set.univ 0 T,
      parabolicDistance p q ≤ r →
      ‖spatialDD (fun z : Point n => heatDuhamel g z.2 z.1) p-
        spatialDD (fun z : Point n => heatDuhamel g z.2 z.1) q‖ ≤ C*diniBudget psi r := by
  obtain ⟨Cs,hCs,hSpace⟩ := heatDuhamel_spatial_dini_bound (n := n)
  obtain ⟨Ct,hCt,hTime⟩ := heatDuhamel_temporal_dini_bound (n := n)
  refine ⟨Cs+Ct,by positivity,?_⟩
  intro T eta G F B g psi hT hT1 he he1 hG0 hF hB hg hG hm hz hmono hp hmod r hr p hpm q hqm hpq
  let ghat : Point n → ℝ := fun z => g (z.1,max 0 (min z.2 T))
  have hhat : HolderBound eta Set.univ ghat F := holderBound_timeClamp he.le hT.le hg
  have hc : Continuous ghat := continuousOn_univ.mp (holderBound_continuousOn he hhat)
  have hBound (z : Point n) : |ghat z| ≤ G :=
    hG _ ⟨Set.mem_univ _,le_max_left _ _,max_le hT.le (min_le_right _ _)⟩
  have hMod (a : ℝ) (x y : Space n) : |ghat (x,a)-ghat (y,a)| ≤ psi ‖x-y‖ :=
    hmod _ ⟨le_max_left _ _,max_le hT.le (min_le_right _ _)⟩ x y
  have heq (a : ℝ) (ha : a ∈ Set.Icc 0 T) : heatDuhamel ghat a=heatDuhamel g a :=
    funext (heatDuhamel_timeClamp g ha)
  have hsp : ‖p.1-q.1‖ ≤ r := by
    apply le_trans _ hpq
    exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have htm : |p.2-q.2| ≤ r^2 := by
    have hsr : Real.sqrt |p.2-q.2| ≤ r :=
      (le_add_of_nonneg_left (norm_nonneg (p.1-q.1))).trans hpq
    have hsq := Real.sq_sqrt (abs_nonneg (p.2-q.2))
    nlinarith only [hsr,hsq,Real.sqrt_nonneg |p.2-q.2|,hr]
  have hs := hSpace eta B G ghat psi he he1 hB hc hBound hm hz hmono hp hMod p.2 hpm.2.1 r hr q.1 (p.1-q.1) hsp
  have harg : q.1+(p.1-q.1)=p.1 := by abel
  rw [harg] at hs
  have ht : ‖fderiv ℝ (fderiv ℝ (heatDuhamel ghat p.2)) q.1-
      fderiv ℝ (fderiv ℝ (heatDuhamel ghat q.2)) q.1‖ ≤ Ct*diniBudget psi r := by
    rcases le_total q.2 p.2 with hqp | hpqtime
    · have hd : p.2-q.2 ≤ r^2 := (le_abs_self _).trans htm
      exact hTime eta B G ghat psi he he1 hB hc hBound hm hz hmono hp hMod q.2 p.2 r hqm.2.1 hqp hr hd q.1
    · have hd : q.2-p.2 ≤ r^2 := by rw [← neg_sub]; exact (neg_le_abs _).trans htm
      rw [norm_sub_rev]
      exact hTime eta B G ghat psi he he1 hB hc hBound hm hz hmono hp hMod p.2 q.2 r hpm.2.1 hpqtime hr hd q.1
  change ‖fderiv ℝ (fderiv ℝ (heatDuhamel g p.2)) p.1-
    fderiv ℝ (fderiv ℝ (heatDuhamel g q.2)) q.1‖ ≤ _
  rw [← heq p.2 hpm.2,← heq q.2 hqm.2]
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ (heatDuhamel ghat p.2)) p.1-
        fderiv ℝ (fderiv ℝ (heatDuhamel ghat p.2)) q.1‖+
        ‖fderiv ℝ (fderiv ℝ (heatDuhamel ghat p.2)) q.1-
        fderiv ℝ (fderiv ℝ (heatDuhamel ghat q.2)) q.1‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ Cs*diniBudget psi r+Ct*diniBudget psi r := add_le_add hs ht
    _ = _ := by ring

end Yau.LeafProofs.L05Aux
