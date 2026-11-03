import Yau.LeafProofs.L05DiniKernelOldTime

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

local instance l05DiniKernelPotentialDualGroup (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance l05DiniKernelPotentialDualSpace (n : ℕ) : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance l05DiniKernelPotentialHessianGroup (n : ℕ) : NormedAddCommGroup (DiniHessian n) := inferInstance
local instance l05DiniKernelPotentialHessianSpace (n : ℕ) : NormedSpace ℝ (DiniHessian n) := inferInstance

theorem heatDuhamel_spatialDD_cancelled {n : ℕ} {T eta G F : ℝ} {g : Point n → ℝ}
    (hT : 0 < T) (he : 0 < eta) (hg : HolderBound eta (cylinder Set.univ 0 T) g F)
    (hG : ∀ p ∈ cylinder Set.univ 0 T, |g p| ≤ G)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : Space n) :
    spatialDD (fun p : Point n => L16Aux.heatDuhamel g p.2 p.1) (x,t) =
      ∫ s in (0:ℝ)..t, ∫ y : Space n, (g (x-y,s)-g (x,s)) • diniHeatD2 (t-s) y := by
  change fderiv ℝ (fderiv ℝ (L16Aux.heatDuhamel g t)) x = _
  rcases ht.1.eq_or_lt with hzero | ht0
  · have htzero : t=0 := hzero.symm
    subst t
    have hz : L16Aux.heatDuhamel g 0 = fun _ : Space n => (0:ℝ) :=
      funext (L16Aux.heatDuhamel_zero g)
    simp only [hz,fderiv_fun_const,intervalIntegral.integral_same]
    exact fderiv_const_apply (0 : Space n →L[ℝ] ℝ)
  let ghat : Point n → ℝ := fun p => g (p.1,max 0 (min p.2 T))
  have hhat : HolderBound eta Set.univ ghat F := L16Aux.holderBound_timeClamp he.le hT.le hg
  have hc : Continuous ghat := continuousOn_univ.mp (L16Aux.holderBound_continuousOn he hhat)
  have hb (p : Point n) : |ghat p| ≤ G :=
    hG _ ⟨Set.mem_univ _,le_max_left _ _,max_le hT.le (min_le_right _ _)⟩
  have hspace (s : ℝ) (x y : Space n) : |ghat (x,s)-ghat (y,s)| ≤ F*‖x-y‖^eta := by
    simpa only [holderWeight,sub_self,abs_zero,
      Real.zero_rpow (by positivity : eta/2 ≠ 0),add_zero,Real.norm_eq_abs] using
      hhat.2.2 (x,s) (Set.mem_univ _) (y,s) (Set.mem_univ _)
  have heq : L16Aux.heatDuhamel ghat t=L16Aux.heatDuhamel g t :=
    funext (L16Aux.heatDuhamel_timeClamp g ht)
  rw [← heq,(L16Aux.heatDuhamel_fderiv_hasFDerivAt he hc hb hg.1 hspace ht0 x).fderiv]
  simp only [intervalIntegral.integral_of_le ht.1,integral_Ioc_eq_integral_Ioo]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  rw [L16Aux.heatAverage_secondFDeriv_cancelled (g := fun y => ghat (y,s)) (sub_pos.mpr hs.2)
    (hc.comp (continuous_id.prodMk continuous_const)) (fun y => hb (y,s)) x]
  have hslice (y : Space n) : ghat (y,s)=g (y,s) :=
    L16Aux.timeClamp_eqOn T g ⟨Set.mem_univ _,hs.1.le,hs.2.le.trans ht.2⟩
  congr 1
  funext y
  rw [hslice,hslice]
  rfl

end Yau.LeafProofs.L05Aux
