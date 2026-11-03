import Yau.LeafProofs.L05DiniKernelGlobal
import Yau.LeafProofs.L05DiniKernelTailSource
import Yau.LeafProofs.L05DiniKernelBudgetComp

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic
open L16Aux

local instance l05DiniKernelTransportDualGroup (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance l05DiniKernelTransportDualSpace (n : ℕ) : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance l05DiniKernelTransportHessianGroup (n : ℕ) : NormedAddCommGroup (DiniHessian n) := inferInstance
local instance l05DiniKernelTransportHessianSpace (n : ℕ) : NormedSpace ℝ (DiniHessian n) := inferInstance

theorem dini_parabolicDistance_linear_le {n : ℕ} (S : Space n →L[ℝ] Space n)
    {b : ℝ} (hb : 1 ≤ b) (hS : ‖S‖ ≤ b) (p q : Point n) :
    parabolicDistance (S p.1,p.2) (S q.1,q.2) ≤ b*parabolicDistance p q := by
  have hx : ‖S p.1-S q.1‖ ≤ b*‖p.1-q.1‖ := by
    rw [← map_sub]
    exact (S.le_opNorm _).trans (mul_le_mul_of_nonneg_right hS (norm_nonneg _))
  have ht := mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg |p.2-q.2|)
  change ‖S p.1-S q.1‖+Real.sqrt |p.2-q.2| ≤ b*(‖p.1-q.1‖+Real.sqrt |p.2-q.2|)
  nlinarith only [hx,ht]

theorem dini_hessianPullback_sub_norm_le {n : ℕ} (S : Space n ≃L[ℝ] Space n)
    {b : ℝ} (hb : 0 ≤ b) (hS : ‖(S : Space n →L[ℝ] Space n)‖ ≤ b)
    (H K : DiniHessian n) : ‖hessianPullback S H-hessianPullback S K‖ ≤ b^2*‖H-K‖ := by
  rw [← map_sub]
  exact (hessianPullback_norm_le S (H-K)).trans
    (mul_le_mul_of_nonneg_right (sq_le_sq₀ (norm_nonneg _) hb |>.mpr hS) (norm_nonneg _))

theorem constantHeatDuhamel_dini_hessian {n : ℕ} (b c : ℝ) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Space n ≃L[ℝ] Space n),
      ‖(S : Space n →L[ℝ] Space n)‖ ≤ c → ‖(S.symm : Space n →L[ℝ] Space n)‖ ≤ b →
      ∀ (T eta G F B : ℝ) (g : Point n → ℝ) (phi : ℝ → ℝ),
      0 < T → T ≤ 1 → 0 < eta → eta < 1 → 0 ≤ G → 0 ≤ F → 0 ≤ B →
      HolderBound eta (cylinder Set.univ 0 T) g F →
      (∀ p ∈ cylinder Set.univ 0 T, |g p| ≤ G) →
      Measurable phi → MonotoneOn phi (Set.Ioc (0:ℝ) 1) → powerBound eta B phi →
      (∀ r ∈ Set.Ioc (0:ℝ) 1, ∀ p ∈ cylinder Set.univ 0 T, ∀ q ∈ cylinder Set.univ 0 T,
        parabolicDistance p q ≤ r → |g p-g q| ≤ phi r) →
      ∀ r ∈ Set.Ioc (0:ℝ) 1, ∀ p ∈ cylinder Set.univ 0 T, ∀ q ∈ cylinder Set.univ 0 T,
        parabolicDistance p q ≤ r →
        ‖spatialDD (constantHeatDuhamel S g) p-spatialDD (constantHeatDuhamel S g) q‖ ≤
          C*(diniTransform phi r+r*G) := by
  obtain ⟨Ce,hCe,hEucl⟩ := heatDuhamel_global_dini_hessian (n := n)
  have hb0 : 0 < b := zero_lt_one.trans_le hb
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  refine ⟨2*Ce*c*b^3,by positivity,?_⟩
  intro S hS hSinv T eta G F B g phi hT hT1 he he1 hG0 hF hB hg hG hm hmono hp hmod r hr p hpm q hqm hpq
  let chi : ℝ → ℝ := diniModulusTail G phi
  let psi : ℝ → ℝ := fun a => chi (c*a)
  let f : Point n → ℝ := spaceTimePullback S g
  let V : Point n → ℝ := fun z => heatDuhamel f z.2 z.1
  have hChi := diniModulusTail_data he he1 hB hG0 hm hmono hp
  have hAmp : 0 ≤ B+2*G := by positivity
  have hPsi := dini_comp_mul_data hAmp hChi.1 hc0 hChi.2.2.2
  have hpsi0 : psi 0=0 := by simpa only [psi,mul_zero] using hChi.2.1
  have hpsiMono : MonotoneOn psi (Set.Ioi (0:ℝ)) :=
    fun a ha d hd had => hChi.2.2.1 (mul_le_mul_of_nonneg_left had hc0.le)
  have hfg : HolderBound eta (cylinder Set.univ 0 T) f (F*(1+‖(S : Space n →L[ℝ] Space n)‖^eta)) :=
    holderBound_comp_spaceLinearMap he.le (S : Space n →L[ℝ] Space n) hg
  have hfBound (z : Point n) (hz : z ∈ cylinder Set.univ 0 T) : |f z| ≤ G :=
    hG _ ⟨Set.mem_univ _,hz.2⟩
  have hfMod (a : ℝ) (ha : a ∈ Set.Icc 0 T) (x y : Space n) :
      |f (x,a)-f (y,a)| ≤ psi ‖x-y‖ := by
    have hh := diniModulusTail_spatial_modulus (hp 1 ⟨by norm_num,le_rfl⟩).1 hG hmod a ha (S x) (S y)
    have hsxy : ‖S x-S y‖ ≤ c*‖x-y‖ := by
      rw [← map_sub]
      exact ((S : Space n →L[ℝ] Space n).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hS (norm_nonneg _))
    exact hh.trans (hChi.2.2.1 hsxy)
  have hdist : parabolicDistance (S.symm p.1,p.2) (S.symm q.1,q.2) ≤ b*r :=
    (dini_parabolicDistance_linear_le (S.symm : Space n →L[ℝ] Space n) hb hSinv p q).trans
      (mul_le_mul_of_nonneg_left hpq hb0.le)
  have hE := hEucl T eta G (F*(1+‖(S : Space n →L[ℝ] Space n)‖^eta)) ((B+2*G)*c^eta)
    f psi hT hT1 he he1 hG0 (by positivity) hPsi.2.1 hfg hfBound hPsi.1 hpsi0 hpsiMono hPsi.2.2
    hfMod (b*r) (mul_pos hb0 hr.1) (S.symm p.1,p.2) ⟨Set.mem_univ _,hpm.2⟩
    (S.symm q.1,q.2) ⟨Set.mem_univ _,hqm.2⟩ hdist
  have hU : constantHeatDuhamel S g=spaceTimePullback S.symm V := rfl
  rw [hU,spatialDD_spaceTimePullback,spatialDD_spaceTimePullback]
  have hPull := dini_hessianPullback_sub_norm_le S.symm hb0.le hSinv
    (spatialDD V (S.symm p.1,p.2)) (spatialDD V (S.symm q.1,q.2))
  have hScale := diniBudget_dilate_le he he1 hAmp hChi.1 hChi.2.2.2 hr.1
    (show (1:ℝ) ≤ c*b from by nlinarith only [mul_le_mul_of_nonneg_right hc hb0.le,hb])
  have hTail := diniModulusTail_budget_le he he1 hB hG0 hm hmono hp hr
  have hNonneg := diniTransform_nonneg_of_powerBound he he1 hB hm hmono hp hr
  calc
    _ ≤ b^2*‖spatialDD V (S.symm p.1,p.2)-spatialDD V (S.symm q.1,q.2)‖ := hPull
    _ ≤ b^2*(Ce*diniBudget psi (b*r)) := mul_le_mul_of_nonneg_left hE (sq_nonneg b)
    _ = b^2*(Ce*diniBudget chi ((c*b)*r)) := by
      rw [diniBudget_comp_mul chi (mul_pos hb0 hr.1) hc0]
      congr 3
      ring
    _ ≤ b^2*(Ce*((c*b)*diniBudget chi r)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hScale hCe.le) (sq_nonneg b)
    _ = (Ce*c*b^3)*diniBudget chi r := by ring
    _ ≤ (Ce*c*b^3)*(diniTransform phi r+2*r*G) :=
      mul_le_mul_of_nonneg_left hTail (by positivity)
    _ ≤ (2*Ce*c*b^3)*(diniTransform phi r+r*G) := by
      have hh := mul_nonneg (show 0 ≤ Ce*c*b^3 by positivity) hNonneg
      nlinarith only [hh]

end Yau.LeafProofs.L05Aux
