import Yau.LeafProofs.L23FieldMetricNormalNeighborhood

/-! Genuine local normal endpoint charts, including global-distance minimality. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem localNormalEndpoint (n : ℕ) : LocalNormalEndpointGap n := by
  intro M h hh c O hO hc
  obtain ⟨B₀,ρ₀,ε,η,e₀,hB₀,hcB₀,hB₀sub,hρ₀,hε,he₀source,he₀eq,hη,he₀inv,hηdata,hηzero⟩ :=
    exists_C3_normal_phase_endpoint h hh c O hO hc
  have h₀ : (0 : ℝ) ∈ Set.Ioo (-ε) (1+ε) := by constructor <;> linarith
  have h₁ : (1 : ℝ) ∈ Set.Ioo (-ε) (1+ε) := by constructor <;> linarith
  have hp₀ : (chartPt c c,(0 : ComplexVector n)) ∈ e₀.source := by
    rw [he₀source]
    exact ⟨hcB₀,Metric.mem_ball_self hρ₀⟩
  have hezero : e₀ (chartPt c c,0) = (chartPt c c,chartPt c c) := by
    calc
      _ = (chartPt c c,(η (chartPt c c,0) 1).1) := he₀eq hp₀
      _ = _ := congrArg (fun p => (chartPt c c,p.1)) ((hηzero _ hcB₀).1 1 h₁)
  have hdiag : (chartPt c c,chartPt c c) ∈ e₀.target := by
    rw [← hezero]
    exact e₀.map_source hp₀
  obtain ⟨B₁,δ,hB₁,hcB₁,hB₁sub,hB₁chart,hδ,hball⟩ :=
    exists_uniform_normal_metric_ball h hh c B₀ hB₀ hcB₀ e₀ hdiag
  let L := ‖realMetricInChart h c (chartPt c c)‖+1
  let C := L+1
  have hL : 0 < L := by dsimp [L]; positivity
  have hC : 0 < C := by dsimp [C]; linarith
  let H := chartTarget c ∩ {z | ‖realMetricInChart h c z‖ < L}
  have hGC : ContinuousOn (fun z : ComplexVector n => ‖realMetricInChart h c z‖) (chartTarget c) :=
    @ContinuousOn.norm (ComplexVector n) (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ)
      inferInstance inferInstance _ _ (realMetricInChart_smooth h hh c).continuousOn
  have hH : IsOpen H := hGC.isOpen_inter_preimage
    (isOpen_extChartAt_target (I := ComplexModel n) c) isOpen_Iio
  have hcH : chartPt c c ∈ H := ⟨mem_extChartAt_target c,by dsimp [L]; linarith⟩
  let B := B₁ ∩ H
  have hB : IsOpen B := hB₁.inter hH
  have hcB : chartPt c c ∈ B := ⟨hcB₁,hcH⟩
  let ρ := min (ρ₀/2) (δ/C)
  have hρ : 0 < ρ := lt_min (half_pos hρ₀) (div_pos hδ hC)
  let D := B ×ˢ Metric.ball (0 : ComplexVector n) ρ
  have hD : IsOpen D := hB.prod Metric.isOpen_ball
  have hDsub : D ⊆ e₀.source := by
    intro p hp
    rw [he₀source]
    refine ⟨hB₁sub hp.1.1,?_⟩
    exact (Metric.ball_subset_ball ((min_le_left (ρ₀/2) (δ/C)).trans (half_le_self hρ₀.le))) hp.2
  have hnorm (p : ComplexVector n × ComplexVector n) (hp : p ∈ D) :
      chartVectorNorm h c p.1 p.2 < δ := by
    have Hnorm := chartVectorNorm_le_opNorm_add_one h c p.1 p.2
    have Hcoef : ‖realMetricInChart h c p.1‖+1 ≤ C := by
      have Hcoef' : ‖realMetricInChart h c p.1‖ < L := hp.1.2.2
      dsimp only [C]
      linarith
    have Hv : ‖p.2‖ < δ/C :=
      (show ‖p.2‖ < ρ by simpa only [Metric.mem_ball,dist_zero_right] using hp.2).trans_le (min_le_right _ _)
    have Hsmall : C*‖p.2‖ < δ := by
      simpa only [mul_comm] using (lt_div_iff₀ hC).mp Hv
    exact (Hnorm.trans (mul_le_mul_of_nonneg_right Hcoef (norm_nonneg _))).trans_lt Hsmall
  let e := e₀.restrOpen D hD
  have hesource : e.source = D := by
    rw [OpenPartialHomeomorph.restrOpen_source]
    exact Set.inter_eq_right.mpr hDsub
  have hetarget : e.target ⊆ e₀.target := by
    intro y hy
    have hp : e.symm y ∈ D := by rw [← hesource]; exact e.map_target hy
    have H := e₀.map_source (hDsub hp)
    have Heval : e₀ (e.symm y) = y := e.right_inv hy
    rwa [Heval] at H
  let X : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n := fun p u => (η p u).1
  have hX : ContDiffOn ℝ 3 (Function.uncurry X) (e.source ×ˢ Set.Ioo (-ε) (1+ε)) :=
    hη.fst.mono (fun p hp => ⟨hDsub (by rw [← hesource]; exact hp.1),hp.2⟩)
  have hη₂ : ContDiffOn ℝ 2 (Function.uncurry η)
      ((B₀ ×ˢ Metric.ball (0 : ComplexVector n) ρ₀) ×ˢ Set.Ioo (-ε) (1+ε)) := by
    rw [← he₀source]
    exact hη.of_le (by norm_num)
  have hi : ∀ p ∈ B₀ ×ˢ Metric.ball (0 : ComplexVector n) ρ₀, η p 0 = p := by
    intro p hp
    exact (hηdata p (by rw [he₀source]; exact hp)).1
  have hs : ∀ p ∈ B₀ ×ˢ Metric.ball (0 : ComplexVector n) ρ₀,
      ∀ u ∈ Set.Ioo (-ε) (1+ε), (η p u).1 ∈ chartTarget c ∧
        HasDerivAt (η p) (chartGeodesicSpray h c (η p u)) u := by
    intro p hp
    exact (hηdata p (by rw [he₀source]; exact hp)).2.1
  refine ⟨B,ρ,ε,X,e,hB,hcB,(fun z hz => hB₁chart hz.1),hρ,hε,hesource,?_,hX,
    he₀inv.mono hetarget,?_,?_⟩
  · intro p hp
    exact he₀eq (hDsub (by rw [← hesource]; exact hp))
  · intro p hp
    have hpD : p ∈ D := by rw [← hesource]; exact hp
    have hpOld : p ∈ e₀.source := hDsub hpD
    have Hp := hηdata p hpOld
    have HD := (ContinuousLinearMap.fst ℝ (ComplexVector n) (ComplexVector n)).hasFDerivAt.comp_hasDerivAt 0
      (Hp.2.1 0 h₀).2
    have HD' : HasDerivAt (X p) p.2 0 := by
      convert! HD using 1
      simp only [chartGeodesicSpray,Hp.1]
      rfl
    refine ⟨congrArg Prod.fst Hp.1,HD'.deriv,(fun u hu => (Hp.2.1 u hu).1),Hp.2.2.1,Hp.2.2.2,?_⟩
    have Hupper := inducedDistance_chartGeodesic_unit_le h hh c (η p) hε Hp.2.1
    rw [Hp.1] at Hupper
    have Hy : inducedDistance h (chartInv c p.1) (chartInv c (η p 1).1) < δ :=
      Hupper.trans_lt (hnorm p hpD)
    have HpB : p.1 ∈ B₀ := hB₁sub hpD.1.1
    have Hz : (η (p.1,0) 1).1 = p.1 := by
      have Hzero := congrArg Prod.fst ((hηzero p.1 HpB).1 1 h₁)
      exact Hzero
    have Hdist := normalEndpoint_distance_on_metric_ball h hh c B₀ hB₀ hB₀sub hρ₀ hε hδ η e₀
      he₀source he₀eq he₀inv hη₂ hi hs p.1 HpB Hz
      (hball p.1 hpD.1.1) (chartInv c (η p 1).1) Hy
    have Hcoord : chartPt c (chartInv c (η p 1).1) = (η p 1).1 :=
      (extChartAt (ComplexModel n) c).right_inv (Hp.2.1 1 h₁).1
    have Hinv : e₀.symm (p.1,(η p 1).1) = p := by
      have Heqp : e₀ p = (p.1,(η p 1).1) := he₀eq hpOld
      rw [← Heqp]
      exact e₀.left_inv hpOld
    rw [Hcoord,Hinv] at Hdist
    exact (congrArg (fun d : ℝ => d^2) Hdist).trans (chartVectorNorm_sq h c p.1 p.2)
  · intro z hz
    have Hz := hηzero z (hB₁sub hz.1)
    exact ⟨fun u hu => congrArg Prod.fst (Hz.1 u hu),Hz.2⟩

end Yau.LeafProofs.L23Aux
