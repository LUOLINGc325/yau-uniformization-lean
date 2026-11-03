import Yau.LeafProofs.L23BernsteinMaximum
import Yau.LeafProofs.L23LocalDistanceSupportCutoff

/-! Compact cylinders and genuine lower supports for the nonlinear maximum estimate. -/

noncomputable section
open Filter
open scoped Topology ContDiff Matrix

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

def ParabolicCutoffLowerSupports (h : ℝ → HermitianField M) (σ : ℝ)
    (η : M.Carrier → ℝ → ℝ) (S : Set M.Carrier) (b T G L : ℝ) : Prop :=
  ∀ x ∈ interior S, ∀ t ∈ Set.Ioc b T, 0 < η x t →
    ∃ ψ : M.Carrier → ℝ → ℝ,
      ContDiffAt ℝ 2 (fun z : ComplexVector n × ℝ => ψ (chartInv x z.1) z.2) (chartPt x x,t) ∧
      ψ x t=η x t ∧ (∀ᶠ z in 𝓝 (x,t), ψ z.1 z.2 ≤ η z.1 z.2) ∧
      realGradPair (h t) (fun y => ψ y t) (fun y => ψ y t) x ≤ G*η x t ∧
      flowOp h σ ψ x t ≤ L

theorem nonlinear_cutoff_maximum
    (h : ℝ → HermitianField M) (σ b T α β G L : ℝ)
    (S : Set M.Carrier) (hS : IsCompact S) (hbT : b < T)
    (hσ : 0 < σ) (hα : 0 < α) (hβ : 0 ≤ β) (hG : 0 ≤ G) (hL : 0 ≤ L)
    (u η : M.Carrier → ℝ → ℝ)
    (hu : ContinuousOn (fun z : M.Carrier × ℝ => u z.1 z.2) (S ×ˢ Set.Icc b T))
    (hη : ContinuousOn (fun z : M.Carrier × ℝ => η z.1 z.2) (S ×ˢ Set.Icc b T))
    (huNonneg : ∀ x ∈ S, ∀ t ∈ Set.Icc b T, 0 ≤ u x t)
    (hηRange : ∀ x ∈ S, ∀ t ∈ Set.Icc b T, 0 ≤ η x t ∧ η x t ≤ 1)
    (hηBoundary : ∀ x ∈ S, x ∉ interior S → ∀ t ∈ Set.Icc b T, η x t=0)
    (huJoint : ∀ x ∈ interior S, ∀ t ∈ Set.Ioc b T,
      ContDiffAt ℝ 2 (fun z : ComplexVector n × ℝ => u (chartInv x z.1) z.2) (chartPt x x,t))
    (hSupports : ParabolicCutoffLowerSupports h σ η S b T G L)
    (huOp : ∀ x ∈ interior S, ∀ t ∈ Set.Ioc b T,
      0 < η x t → flowOp h σ u x t ≤ -σ*α*(u x t)^2+σ*β) :
    ∀ q ∈ S, η q T=1 →
      u q T ≤ 2*(1+(L+σ*G)*(T-b))/(σ*α*(T-b))+Real.sqrt (2*β/α) := by
  intro q hq hqη
  let W : M.Carrier × ℝ → ℝ := fun z => (z.2-b)*η z.1 z.2*u z.1 z.2
  have hW : ContinuousOn W (S ×ˢ Set.Icc b T) :=
    ((continuousOn_snd.sub continuousOn_const).mul hη).mul hu
  have hCompact := hS.prod (isCompact_Icc (a := b) (b := T))
  obtain ⟨p,hp,hmax⟩ := hCompact.exists_isMaxOn
    (f := W) ⟨(q,T),hq,hbT.le,le_rfl⟩ hW
  let x := p.1
  let t := p.2
  have hx : x ∈ S := hp.1
  have ht : t ∈ Set.Icc b T := hp.2
  have hmax' (y : M.Carrier) (hy : y ∈ S) (s : ℝ) (hs : s ∈ Set.Icc b T) :
      (s-b)*η y s*u y s ≤ (t-b)*η x t*u x t := by
    have hm : W (y,s) ≤ W p := hmax ⟨hy,hs⟩
    exact hm
  have hδ : 0 < T-b := sub_pos.mpr hbT
  have hΛ : 0 ≤ L+σ*G := add_nonneg hL (mul_nonneg hσ.le hG)
  have hvalue := hmax' q hq T ⟨hbT.le,le_rfl⟩
  rw [hqη,mul_one] at hvalue
  by_cases hpos : 0 < (t-b)*η x t*u x t
  · have hu0 := huNonneg x hx t ht
    have hηrange := hηRange x hx t ht
    have hbt : b < t := by
      by_contra hnot
      have heq : t=b := le_antisymm (not_lt.mp hnot) ht.1
      rw [heq,sub_self,zero_mul,zero_mul] at hpos
      exact (lt_irrefl 0) hpos
    have hθ : 0 < t-b := sub_pos.mpr hbt
    have hηpos : 0 < η x t := by
      by_contra hnot
      have heq : η x t=0 := le_antisymm (not_lt.mp hnot) hηrange.1
      rw [heq,mul_zero,zero_mul] at hpos
      exact (lt_irrefl 0) hpos
    have huPos : 0 < u x t := by
      by_contra hnot
      have heq : u x t=0 := le_antisymm (not_lt.mp hnot) hu0
      rw [heq,mul_zero] at hpos
      exact (lt_irrefl 0) hpos
    have hxInterior : x ∈ interior S := by
      by_contra hnot
      have heq := hηBoundary x hx hnot t ht
      rw [heq] at hηpos
      exact (lt_irrefl 0) hηpos
    have ht' : t ∈ Set.Ioc b T := ⟨hbt,ht.2⟩
    have hUjoint := huJoint x hxInterior t ht'
    obtain ⟨ψ,hψJoint,hψValue,hψNear,hψGrad,hψOp⟩ := hSupports x hxInterior t ht' hηpos
    have huSpace := distanceSupport_jointC2_space hUjoint
    have hψSpace := distanceSupport_jointC2_space hψJoint
    have huTime := (distanceSupport_jointC2_time hUjoint).differentiableAt (by norm_num)
    have hψTime := (distanceSupport_jointC2_time hψJoint).differentiableAt (by norm_num)
    have hSpaceMap : ContinuousAt (fun y : M.Carrier => (y,t)) x :=
      continuousAt_id.prodMk continuousAt_const
    have hTimeMap : ContinuousAt (fun s : ℝ => (x,s)) t :=
      continuousAt_const.prodMk continuousAt_id
    have huActual := distanceSupport_jointC2_continuousAt hUjoint
    have huSpaceNear : ∀ᶠ y in 𝓝 x, 0 < u y t :=
      (huActual.comp (f := fun y : M.Carrier => (y,t)) hSpaceMap).eventually (Ioi_mem_nhds huPos)
    have huTimeNear : ∀ᶠ s in 𝓝 t, 0 < u x s :=
      (huActual.comp (f := fun s : ℝ => (x,s)) hTimeMap).eventually (Ioi_mem_nhds huPos)
    have hψSpaceNear : ∀ᶠ y in 𝓝 x, ψ y t ≤ η y t := hSpaceMap.eventually hψNear
    have hψTimeNear : ∀ᶠ s in 𝓝 t, ψ x s ≤ η x s := hTimeMap.eventually hψNear
    have hSnear : ∀ᶠ y in 𝓝 x, y ∈ S := mem_interior_iff_mem_nhds.mp hxInterior
    have hSpaceActual : IsLocalMax (fun y => ψ y t*u y t) x := by
      filter_upwards [hSnear,hψSpaceNear,huSpaceNear] with y hy hψy huy
      have hηMax : η y t*u y t ≤ η x t*u x t := by
        apply (mul_le_mul_iff_right₀ hθ).mp
        simpa only [mul_assoc,mul_comm,mul_left_comm] using hmax' y hy t ht
      calc
        ψ y t*u y t ≤ η y t*u y t := mul_le_mul_of_nonneg_right hψy huy.le
        _ ≤ η x t*u x t := hηMax
        _ = ψ x t*u x t := by rw [hψValue]
    have hInv : chartInv x (chartPt x x)=x :=
      (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
    have hChartLim : Tendsto (chartInv x) (𝓝 (chartPt x x)) (𝓝 x) := by
      have hc : ContinuousAt (chartInv x) (chartPt x x) :=
        continuousAt_extChartAt_symm'' (I := ComplexModel n) (mem_extChartAt_target x)
      simpa only [hInv] using hc.tendsto
    have hSpaceMax : IsLocalMax
        (fun z => inChart x (fun y => ψ y t) z*inChart x (fun y => u y t) z) (chartPt x x) := by
      change ∀ᶠ z in 𝓝 (chartPt x x), ψ (chartInv x z) t*u (chartInv x z) t ≤
        ψ (chartInv x (chartPt x x)) t*u (chartInv x (chartPt x x)) t
      simpa only [hInv] using hChartLim.eventually hSpaceActual
    have hTimeMax : IsLocalMaxOn (fun s => (s-b)*ψ x s*u x s) (Set.Iic t) t := by
      have hBnear : ∀ᶠ s in 𝓝 t, b < s := Ioi_mem_nhds hbt
      filter_upwards [hBnear.filter_mono nhdsWithin_le_nhds,
        hψTimeNear.filter_mono nhdsWithin_le_nhds,
        huTimeNear.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with s hbs hψs hus hst
      have hs : s ∈ Set.Icc b T := ⟨hbs.le,hst.trans ht.2⟩
      calc
        (s-b)*ψ x s*u x s ≤ (s-b)*η x s*u x s :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hψs (sub_nonneg.mpr hbs.le)) hus.le
        _ ≤ (t-b)*η x t*u x t := hmax' x hx s hs
        _ = (t-b)*ψ x t*u x t := by rw [hψValue]
    have hPoint := nonlinear_cutoff_pointwise h σ b t α β G L u ψ x hσ hθ hu0
      (by rwa [hψValue]) huSpace hψSpace huTime hψTime hSpaceMax hTimeMax
      (by rwa [hψValue]) (huOp x hxInterior t ht' hηpos) hψOp
    rw [hψValue] at hPoint
    have hQuad := nonlinear_cutoff_quadratic hσ hα hβ hΛ hθ
      (sub_le_sub_right ht.2 b) hηpos hηrange.2 hu0 hPoint
    have hBound := nonlinear_maximum_bound_of_quadratic hσ hα hβ hΛ hδ hpos.le hQuad
    have hCenter : u q T ≤ ((t-b)*η x t*u x t)/(T-b) := by
      apply (le_div_iff₀ hδ).mpr
      simpa only [mul_comm] using hvalue
    exact hCenter.trans hBound
  · have hCenter : u q T ≤ 0 := by
      have hnonpos := not_lt.mp hpos
      have hh : (T-b)*u q T ≤ 0 := hvalue.trans hnonpos
      nlinarith
    exact hCenter.trans (by positivity)

end Yau.LeafProofs.L23Aux
