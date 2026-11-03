import Yau.LeafProofs.L23FieldMetricEndpointFirstVariation

/-! Actual endpoint branches inherit the two-endpoint energy derivative. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 800000

theorem chartEndpointEnergy_hasDerivAt
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier)
    (D : Set (ComplexVector n × ComplexVector n)) {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε)
    (η : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n × ComplexVector n)
    (hη : ContDiffOn ℝ 2 (Function.uncurry η) (D ×ˢ Set.Ioo (-ε) (1+ε)))
    (hi : ∀ p ∈ D, η p 0 = p)
    (hs : ∀ p ∈ D, ∀ u ∈ Set.Ioo (-ε) (1+ε), (η p u).1 ∈ chartTarget c ∧
      HasDerivAt (η p) (chartGeodesicSpray h c (η p u)) u)
    (p : ℝ → ComplexVector n × ComplexVector n)
    (hp : ContDiffOn ℝ 2 p (Set.Ioo (-a) a))
    (hmap : Set.MapsTo p (Set.Ioo (-a) a) D) :
    HasDerivAt (fun r => chartGeodesicEnergy h c (p r))
      (2*(realMetricInChart h c (η (p 0) 1).1 (η (p 0) 1).2
          (deriv (fun r => (η (p r) 1).1) 0)-
        realMetricInChart h c (p 0).1 (p 0).2 (deriv (fun r => (p r).1) 0))) 0 := by
  let I := Set.Ioo (-a) a
  let J := Set.Ioo (-ε) (1+ε)
  have h₀I : (0 : ℝ) ∈ I := ⟨by linarith,ha⟩
  have h₀J : (0 : ℝ) ∈ J := ⟨by linarith,by linarith⟩
  let ζ : ℝ × ℝ → ComplexVector n × ComplexVector n := fun q => η (p q.1) q.2
  have hpjoint : ContDiffOn ℝ 2 (fun q : ℝ × ℝ => (p q.1,q.2)) (I ×ˢ J) :=
    (hp.comp contDiffOn_fst (fun q hq => hq.1)).prodMk contDiffOn_snd
  have hζ : ContDiffOn ℝ 2 ζ (I ×ˢ J) :=
    hη.comp hpjoint (fun q hq => ⟨hmap hq.1,hq.2⟩)
  have hinitial : η (p 0) 0 = p 0 := hi _ (hmap h₀I)
  have hz : (p 0).1 ∈ chartTarget c := by
    rw [← hinitial]
    exact (hs _ (hmap h₀I) 0 h₀J).1
  have hE : DifferentiableAt ℝ (chartGeodesicEnergy h c) (p 0) :=
    ((chartGeodesicEnergy_contDiffOn h hh c).contDiffAt
      (((isOpen_extChartAt_target (I := ComplexModel n) c).prod isOpen_univ).mem_nhds
        ⟨hz,Set.mem_univ _⟩)).differentiableAt (by simp)
  have hpD : HasDerivAt p (deriv p 0) 0 :=
    ((hp.contDiffAt (isOpen_Ioo.mem_nhds h₀I)).differentiableAt (by norm_num)).hasDerivAt
  have HD := hE.hasFDerivAt.comp_hasDerivAt 0 hpD
  have hEq : (fun r => chartGeodesicEnergy h c (ζ (r,0))) =ᶠ[𝓝 (0 : ℝ)]
      (fun r => chartGeodesicEnergy h c (p r)) := by
    filter_upwards [isOpen_Ioo.mem_nhds h₀I] with r hr
    exact congrArg (chartGeodesicEnergy h c) (hi _ (hmap hr))
  have HE := chartGeodesic_variation_firstVariation h hh c ζ ha hε hζ
    (fun r hr u hu => hs _ (hmap hr) u hu) (HD.congr_of_eventuallyEq hEq)
  have hInitPos : (fun r => (ζ (r,0)).1) =ᶠ[𝓝 (0 : ℝ)] (fun r => (p r).1) := by
    filter_upwards [isOpen_Ioo.mem_nhds h₀I] with r hr
    exact congrArg Prod.fst (hi _ (hmap hr))
  change 2*(realMetricInChart h c (η (p 0) 1).1 (η (p 0) 1).2
    (deriv (fun r => (η (p r) 1).1) 0)-realMetricInChart h c (η (p 0) 0).1 (η (p 0) 0).2
      (deriv (fun r => (ζ (r,0)).1) 0)) = fderiv ℝ (chartGeodesicEnergy h c) (p 0) (deriv p 0) at HE
  rw [hinitial,hInitPos.deriv_eq] at HE
  rw [← HE] at HD
  exact HD

end Yau.LeafProofs.L23Aux
