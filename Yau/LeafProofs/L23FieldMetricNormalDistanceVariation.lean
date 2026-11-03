import Yau.LeafProofs.L23FieldMetricNormalDistanceSmooth

/-! The actual local distance squared has the two-endpoint first variation. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 800000

theorem normalEndpoint_distanceSq_hasDerivAt
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier)
    (X : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n)
    (e : OpenPartialHomeomorph (ComplexVector n × ComplexVector n) (ComplexVector n × ComplexVector n))
    {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε)
    (he : Set.EqOn e (fun p => (p.1,X p 1)) e.source)
    (hinv : ContDiffOn ℝ 3 e.symm e.target)
    (hX : ContDiffOn ℝ 3 (Function.uncurry X) (e.source ×ˢ Set.Ioo (-ε) (1+ε)))
    (hi : ∀ p ∈ e.source, X p 0 = p.1 ∧ deriv (X p) 0 = p.2)
    (htarget : ∀ p ∈ e.source, ∀ u ∈ Set.Ioo (-ε) (1+ε), X p u ∈ chartTarget c)
    (hgeo : ∀ p ∈ e.source,
      FieldGeodesicOn h (fun u => chartInv c (X p u)) (Set.Ioo (-ε) (1+ε)))
    (hmin : ∀ p ∈ e.source,
      inducedDistance h (chartInv c p.1) (chartInv c (X p 1))^2 = realMetricInChart h c p.1 p.2 p.2)
    (Q : ℝ → ComplexVector n × ComplexVector n)
    (hQ : ContDiffOn ℝ 2 Q (Set.Ioo (-a) a))
    (hQmap : Set.MapsTo Q (Set.Ioo (-a) a) e.target) :
    HasDerivAt (fun r => inducedDistance h (chartInv c (Q r).1) (chartInv c (Q r).2)^2)
      (2*(realMetricInChart h c (Q 0).2 (normalFamilyPhase X (e.symm (Q 0)) 1).2
          (deriv (fun r => (Q r).2) 0)-
        realMetricInChart h c (Q 0).1 (e.symm (Q 0)).2 (deriv (fun r => (Q r).1) 0))) 0 := by
  let P : ℝ → ComplexVector n × ComplexVector n := fun r => e.symm (Q r)
  let J := Set.Ioo (-ε) (1+ε)
  have h₀I : (0 : ℝ) ∈ Set.Ioo (-a) a := ⟨by linarith,ha⟩
  have h₀J : (0 : ℝ) ∈ J := ⟨by linarith,by linarith⟩
  have hP : ContDiffOn ℝ 2 P (Set.Ioo (-a) a) := (hinv.of_le (by norm_num)).comp hQ hQmap
  have hPmap : Set.MapsTo P (Set.Ioo (-a) a) e.source := fun r hr => e.map_target (hQmap hr)
  have hPhase := normalFamilyPhase_contDiffOn X e.open_source isOpen_Ioo hX
  have hInit : ∀ p ∈ e.source, normalFamilyPhase X p 0 = p :=
    normalFamilyPhase_initial X e.open_source isOpen_Ioo h₀J hX hi
  have hSol : ∀ p ∈ e.source, ∀ u ∈ J,
      (normalFamilyPhase X p u).1 ∈ chartTarget c ∧
        HasDerivAt (normalFamilyPhase X p) (chartGeodesicSpray h c (normalFamilyPhase X p u)) u := by
    intro p hp u hu
    exact ⟨htarget p hp u hu,
      normalFamilyPhase_is_solution h c X e.open_source isOpen_Ioo hX htarget hgeo p hp u hu⟩
  have HD := chartEndpointEnergy_hasDerivAt h hh c e.source ha hε (normalFamilyPhase X)
    hPhase hInit hSol P hP hPmap
  have hFirst : (fun r => (P r).1) =ᶠ[𝓝 (0 : ℝ)] (fun r => (Q r).1) := by
    filter_upwards [isOpen_Ioo.mem_nhds h₀I] with r hr
    have H := (he (hPmap hr)).symm.trans (e.right_inv (hQmap hr))
    have Hp := congrArg Prod.fst H
    exact Hp
  have hLast : (fun r => (normalFamilyPhase X (P r) 1).1) =ᶠ[𝓝 (0 : ℝ)] (fun r => (Q r).2) := by
    filter_upwards [isOpen_Ioo.mem_nhds h₀I] with r hr
    have H := (he (hPmap hr)).symm.trans (e.right_inv (hQmap hr))
    exact congrArg Prod.snd H
  have hEnergyEq : (fun r => inducedDistance h (chartInv c (Q r).1) (chartInv c (Q r).2)^2) =ᶠ[𝓝 (0 : ℝ)]
      (fun r => chartGeodesicEnergy h c (P r)) := by
    filter_upwards [isOpen_Ioo.mem_nhds h₀I] with r hr
    exact normalEndpoint_distanceSq_eq_energy h c X e he hmin (hQmap hr)
  have hFirst0 : (P 0).1 = (Q 0).1 := hFirst.self_of_nhds
  have hLast0 : (normalFamilyPhase X (P 0) 1).1 = (Q 0).2 := hLast.self_of_nhds
  rw [hFirst.deriv_eq,hLast.deriv_eq,hFirst0,hLast0] at HD
  exact HD.congr_of_eventuallyEq hEnergyEq

end Yau.LeafProofs.L23Aux
