import Yau.LeafProofs.L23LocalDistanceSupportNormalEdgesLength
import Yau.LeafProofs.L23LocalDistanceSupportPolygonLength
import Yau.LeafProofs.L23FieldMetricChainLength
import Yau.LeafProofs.L23FieldMetricGeodesicScale

/-! Compact confinement of actual near-minimizers yields an actual short minimizing geodesic. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold ENNReal
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
set_option maxHeartbeats 1200000

theorem compactMinimizingGeodesic (n : ℕ) : CompactMinimizingGeodesicGap n := by
  intro M h hh O S hO hS hSO q y hnear
  letI := manifold_realSmooth M
  obtain ⟨N,v,hv,heq,hmin,hbranches⟩ := exists_compact_normal_polygon h hh O S hO hS hSO q y hnear
  obtain ⟨ε,γ,hdata,hphase⟩ := exists_normal_polygon_edges_matching_phase_length h hh O q y v hmin hbranches
  have hmatch : ∀ j : Fin N, γ j.castSucc 1 = γ j.succ 0 ∧
      geoChartState (γ j.castSucc) (γ j.castSucc 1) 1 = geoChartState (γ j.succ) (γ j.castSucc 1) 0 := by
    intro j
    have HL : γ j.castSucc 1 = v j :=
      (hdata j.castSucc).2.2.1.trans (fieldPolygonPoint_interior q y v j)
    have HR : γ j.succ 0 = v j := by
      have H := (hdata j.succ).2.1
      have Hidx : j.succ.castSucc = j.castSucc.succ := rfl
      rw [Hidx,fieldPolygonPoint_interior] at H
      exact H
    refine ⟨HL.trans HR.symm,?_⟩
    rw [HL]
    exact hphase j
  obtain ⟨δ,hδ,hΓGeo,hΓMap,hΓEq⟩ := unitGeodesicChain_geodesic h hh O N ε γ
    (fun i => ⟨(hdata i).1,(hdata i).2.2.2.1,(hdata i).2.2.2.2.1⟩) hmatch
  let Γ := unitGeodesicChain N γ
  let k : ℝ := (N+1 : ℕ)
  have hk : 0 < k := by dsimp [k]; positivity
  let δhat := δ/k
  have hδhat : 0 < δhat := div_pos hδ hk
  let γhat : ℝ → M.Carrier := fun t => Γ (k*t)
  have hδmul : k*(δ/k) = δ := by field_simp [hk.ne']
  have hhatGeo : FieldGeodesicOn h γhat (Set.Ioo (-δhat) (1+δhat)) := by
    apply fieldGeodesicOn_mono h γhat (fieldGeodesicOn_mul h Γ _ hΓGeo k)
    intro t ht
    change -δ < k*t ∧ k*t < k+δ
    have Hlo := mul_lt_mul_of_pos_left ht.1 hk
    have Hhi := mul_lt_mul_of_pos_left ht.2 hk
    dsimp only [δhat] at Hlo Hhi
    constructor <;> nlinarith only [Hlo,Hhi,hδmul]
  have hΓ₀ : Γ 0 = q := by
    have Hnear := hΓEq (0 : Fin (N+1)) 0 (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num)
    have Hpoint : Γ 0 = γ 0 0 := by
      simpa only [Fin.val_zero,Nat.cast_zero,zero_add,add_zero,sub_zero] using Hnear.self_of_nhds
    have Hstart : γ 0 0 = q := (hdata 0).2.1
    exact Hpoint.trans Hstart
  have hΓk : Γ k = y := by
    have Hnear := hΓEq (Fin.last N) 1 (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num)
    have Hcenter : ((Fin.last N).val : ℝ)+1 = k := by simp only [Fin.val_last]; dsimp only [k]; push_cast; rfl
    rw [Hcenter] at Hnear
    have Harg : k-((Fin.last N).val : ℝ) = 1 := by
      dsimp only [k]
      simp only [Fin.val_last,Nat.cast_add,Nat.cast_one]
      ring
    have Hpoint : Γ k = γ (Fin.last N) 1 := by simpa only [Harg] using Hnear.self_of_nhds
    have Hfinish := (hdata (Fin.last N)).2.2.1
    simp only [fieldPolygonPoint,Fin.cases_succ,Fin.lastCases_last] at Hfinish
    exact Hpoint.trans Hfinish
  have hhat₀ : γhat 0 = q := by change Γ (k*0) = q; rw [mul_zero,hΓ₀]
  have hhat₁ : γhat 1 = y := by change Γ (k*1) = y; rw [mul_one,hΓk]
  have hhatMap : Set.MapsTo γhat (Set.Icc (0 : ℝ) 1) O := by
    intro t ht
    apply hΓMap
    exact ⟨mul_nonneg hk.le ht.1,(mul_le_mul_of_nonneg_left ht.2 hk.le).trans_eq (mul_one k)⟩
  have hγDiff : ∀ i, MDifferentiableOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) (γ i) (Set.Icc (0 : ℝ) 1) := by
    intro i
    have HC : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 (γ i) (Set.Icc (0 : ℝ) 1) :=
      ((hdata i).2.2.2.1.1.of_le (by norm_num)).mono
        (fun t ht => ⟨by linarith [(hdata i).1,ht.1],by linarith [(hdata i).1,ht.2]⟩)
    exact HC.mdifferentiableOn (by norm_num)
  have HΓLength : fieldPathELength h Γ 0 k = ENNReal.ofReal (inducedDistance h q y) := by
    calc
      _ = ∑ i : Fin (N+1), fieldPathELength h (γ i) 0 1 := fieldPathELength_chain_eq_sum h N Γ γ hΓEq hγDiff
      _ = ∑ i : Fin (N+1), ENNReal.ofReal (inducedDistance h
          (fieldPolygonPoint q y v i.castSucc) (fieldPolygonPoint q y v i.succ)) :=
        Finset.sum_congr rfl (fun i _ => (hdata i).2.2.2.2.2)
      _ = ENNReal.ofReal (∑ i : Fin (N+1), inducedDistance h
          (fieldPolygonPoint q y v i.castSucc) (fieldPolygonPoint q y v i.succ)) :=
        (ENNReal.ofReal_sum_of_nonneg (fun i _ => inducedDistance_nonneg h hh _ _)).symm
      _ = _ := congrArg ENNReal.ofReal (fieldPolygon_sum_dist_eq_of_energy_eq h hh q y v heq)
  have hΓDiff : MDifferentiableOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) Γ (Set.Icc (0 : ℝ) k) := by
    have HC : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 Γ (Set.Icc (0 : ℝ) k) :=
      (hΓGeo.1.of_le (by norm_num)).mono (fun t ht => ⟨by linarith [ht.1],by linarith [ht.2]⟩)
    exact HC.mdifferentiableOn (by norm_num)
  have HhatLength : fieldPathELength h γhat 0 1 = ENNReal.ofReal (inducedDistance h q y) := by
    have HD : MDifferentiableOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) Γ (Set.Icc (k*0) (k*1)) := by
      simpa only [mul_zero,mul_one] using hΓDiff
    have H := fieldPathELength_comp_mul h Γ 0 1 k zero_le_one hk.le HD
    rw [mul_zero,mul_one,HΓLength] at H
    exact H
  have HspeedLength := fieldGeodesic_unit_pathELength h hh γhat hδhat hhatGeo
  have HsqrtEq : ENNReal.ofReal (Real.sqrt (actualSpeedSq h γhat 0)) = ENNReal.ofReal (inducedDistance h q y) :=
    HspeedLength.symm.trans HhatLength
  have Hsqrt : Real.sqrt (actualSpeedSq h γhat 0) = inducedDistance h q y :=
    le_antisymm ((ENNReal.ofReal_le_ofReal_iff (inducedDistance_nonneg h hh q y)).mp HsqrtEq.le)
      ((ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg _)).mp HsqrtEq.ge)
  have Hspeed₀ : actualSpeedSq h γhat 0 = inducedDistance h q y^2 := by
    have H := congrArg (fun r : ℝ => r^2) Hsqrt
    rwa [Real.sq_sqrt (actualSpeedSq_nonneg h γhat 0)] at H
  refine ⟨δhat,hδhat,γhat,hhat₀,hhat₁,hhatGeo,hhatMap,?_⟩
  intro u hu
  have hu' : u ∈ Set.Ioo (-δhat) (1+δhat) := by constructor <;> linarith [hu.1,hu.2]
  have h₀ : (0 : ℝ) ∈ Set.Ioo (-δhat) (1+δhat) := by constructor <;> linarith
  exact (fieldGeodesic_actualSpeedSq_constant h hh γhat hhatGeo hu' h₀).trans Hspeed₀

end Yau.LeafProofs.L23Aux
