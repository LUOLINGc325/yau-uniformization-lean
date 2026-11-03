import Yau.Proofs.F03LocalSmoothExtension
import Yau.Proofs.F03GradientPositive
import spec.CHAIN.HeatConcreteBindings

/-! Genuine global compact tests from the original smooth-domain defining data. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

theorem exists_boundary_defining_tests (g : HermitianField M)
    (Ω : Set M.Carrier) (hΩ : SmoothPrecompactDomain Ω) (p : M.Carrier) (hp : p ∈ frontier Ω) :
    ∃ (a : M.Carrier) (r q : M.Carrier → ℝ) (W : Set (ComplexVector n)),
      p ∈ (extChartAt (ComplexModel n) a).source ∧
      SmoothFn r ∧ HasCompactSupport r ∧ SmoothFn q ∧ HasCompactSupport q ∧
      IsOpen W ∧ chartPt a p ∈ W ∧ W ⊆ chartTarget a ∧
      r p=0 ∧ q p=0 ∧ 0 < LeafProofs.L18Aux.scalarGradientPair g r r p ∧
      (∀ z ∈ W, chartInv a z ∈ Ω → 0 < r (chartInv a z)) ∧
      (∀ z ∈ W, q (chartInv a z)=‖z-chartPt a p‖^2) := by
  obtain ⟨a,V,ρ,hpsrc,hV,hpV,hVt,hρ,hρzero,hDρ,hLocal⟩ := hΩ.2.2.2.2 p hp
  have hpsrc' : p ∈ (extChartAt (ComplexModel n) a).source := by
    simpa only [extChartAt_source] using hpsrc
  have hinv : chartInv a (chartPt a p)=p := (extChartAt (ComplexModel n) a).left_inv hpsrc'
  obtain ⟨r,Wr,hr,hcr,hWr,hpWr,hWrV,hReq⟩ :=
    exists_local_smooth_compact_extension a hV hVt hpV hρ.neg
  have hNorm : ContDiff ℝ ∞ (fun z : ComplexVector n => ‖z-chartPt a p‖^2) :=
    (contDiff_id.sub contDiff_const).norm_sq ℝ
  obtain ⟨q,Wq,hq,hcq,hWq,hpWq,hWqV,hQeq⟩ :=
    exists_local_smooth_compact_extension a hV hVt hpV hNorm.contDiffOn
  let W := Wr ∩ Wq
  have hWV : W ⊆ V := inter_subset_left.trans (subset_closure.trans hWrV)
  have hrzero : r p=0 := by
    have h := hReq (chartPt a p) hpWr
    simpa only [hinv,hρzero,neg_zero] using h
  have hqzero : q p=0 := by
    have h := hQeq (chartPt a p) hpWq
    simpa only [hinv,sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0)] using h
  have hrEq : inChart a r =ᶠ[𝓝 (chartPt a p)] fun z => -ρ z := by
    filter_upwards [hWr.mem_nhds hpWr] with z hz
    exact hReq z hz
  have hDr : fderiv ℝ (inChart a r) (chartPt a p) ≠ 0 := by
    rw [hrEq.fderiv_eq (𝕜 := ℝ)]
    change fderiv ℝ (-ρ) (chartPt a p) ≠ 0
    rw [fderiv_neg]
    exact neg_ne_zero.mpr hDρ
  have hGrad := scalarGradientPair_self_pos_of_chart_fderiv_ne_zero g hr a (hVt hpV) hDr
  rw [hinv] at hGrad
  refine ⟨a,r,q,W,hpsrc',hr,hcr,hq,hcq,hWr.inter hWq,⟨hpWr,hpWq⟩,
    hWV.trans hVt,hrzero,hqzero,hGrad,?_,?_⟩
  · intro z hz hzΩ
    rw [hReq z hz.1]
    exact neg_pos.mpr ((hLocal z (hWV hz)).mp hzΩ)
  · intro z hz
    exact hQeq z hz.2

end Yau.Proofs.F03Aux
