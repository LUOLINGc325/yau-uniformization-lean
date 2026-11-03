import Yau.LeafProofs.L23FieldMetricFirstVariation

/-! Gauss's first variation identity for actual families of chart geodesics. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 800000

theorem chartGeodesic_variation_gauss
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier)
    (ζ : ℝ × ℝ → ComplexVector n × ComplexVector n)
    (z v w : ComplexVector n) {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε)
    (hζ : ContDiffOn ℝ 2 ζ (Set.Ioo (-a) a ×ˢ Set.Ioo (-ε) (1+ε)))
    (hi : ∀ r ∈ Set.Ioo (-a) a, ζ (r,0) = (z,v+r • w))
    (hs : ∀ r ∈ Set.Ioo (-a) a, ∀ u ∈ Set.Ioo (-ε) (1+ε),
      (ζ (r,u)).1 ∈ chartTarget c ∧
        HasDerivAt (fun t => ζ (r,t)) (chartGeodesicSpray h c (ζ (r,u))) u)
    {t : ℝ} (ht : t ∈ Set.Ioo (-ε) (1+ε)) :
    realMetricInChart h c (ζ (0,t)).1 (ζ (0,t)).2
      (deriv (fun r => (ζ (r,t)).1) 0) = t*realMetricInChart h c z v w := by
  let I := Set.Ioo (-a) a
  let J := Set.Ioo (-ε) (1+ε)
  let Z : ℝ × ℝ → ComplexVector n := fun p => (ζ p).1
  let T : ℝ × ℝ → ComplexVector n := fun p => (ζ p).2
  let V : ℝ → ComplexVector n := fun u => deriv (fun r => Z (r,u)) 0
  let W : ℝ → ComplexVector n := fun u => deriv (fun r => T (r,u)) 0
  have h₀I : (0 : ℝ) ∈ I := ⟨by linarith,ha⟩
  have h₀J : (0 : ℝ) ∈ J := ⟨by linarith,by linarith⟩
  have hDopen : IsOpen (I ×ˢ J) := isOpen_Ioo.prod isOpen_Ioo
  have hZ : ContDiffOn ℝ 2 Z (I ×ˢ J) := hζ.fst
  have hT : ContDiffOn ℝ 2 T (I ×ˢ J) := hζ.snd
  have hZtime (u : ℝ) (hu : u ∈ J) :
      HasDerivAt (fun s => Z (0,s)) (T (0,u)) u := by
    convert! (ContinuousLinearMap.fst ℝ (ComplexVector n) (ComplexVector n)).hasFDerivAt.comp_hasDerivAt u
      (hs 0 h₀I u hu).2 using 1
  have hTtime (u : ℝ) (hu : u ∈ J) :
      HasDerivAt (fun s => T (0,s))
        (-chartChristoffelBilin h c (Z (0,u)) (T (0,u)) (T (0,u))) u := by
    convert! (ContinuousLinearMap.snd ℝ (ComplexVector n) (ComplexVector n)).hasFDerivAt.comp_hasDerivAt u
      (hs 0 h₀I u hu).2 using 1
    exact (chartGeodesicAcceleration_eq h c (Z (0,u)) (T (0,u))).symm
  have hRZ (u : ℝ) (hu : u ∈ J) : HasDerivAt (fun r => Z (r,u)) (V u) 0 := by
    exact (((hZ.contDiffAt (hDopen.mem_nhds ⟨h₀I,hu⟩)).comp 0
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by norm_num)).hasDerivAt
  have hRT (u : ℝ) (hu : u ∈ J) : HasDerivAt (fun r => T (r,u)) (W u) 0 := by
    exact (((hT.contDiffAt (hDopen.mem_nhds ⟨h₀I,hu⟩)).comp 0
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by norm_num)).hasDerivAt
  have hVtime (u : ℝ) (hu : u ∈ J) : HasDerivAt V (W u) u := by
    apply mixed_parameter_velocity_hasDerivAt (hZ.contDiffAt (hDopen.mem_nhds ⟨h₀I,hu⟩))
    filter_upwards [hDopen.mem_nhds ⟨h₀I,hu⟩] with p hp
    convert! (ContinuousLinearMap.fst ℝ (ComplexVector n) (ComplexVector n)).hasFDerivAt.comp_hasDerivAt p.2
      (hs p.1 hp.1 p.2 hp.2).2 using 1
  have henergy (u : ℝ) (hu : u ∈ J) :
      realMetricInChart h c (Z (0,u)) (T (0,u))
        (W u+chartChristoffelBilin h c (Z (0,u)) (T (0,u)) (V u)) =
          realMetricInChart h c z v w := by
    have H := chartEnergy_variation_hasDerivAt h hh c
      (z := fun r => Z (r,u)) (T := fun r => T (r,u)) (t := 0)
      (J := V u) (T' := W u) (hs 0 h₀I u hu).1 (hRZ u hu) (hRT u hu)
    have hEq : (fun r => realMetricInChart h c z (v+r • w) (v+r • w)) =ᶠ[𝓝 (0 : ℝ)]
        (fun r => realMetricInChart h c (Z (r,u)) (T (r,u)) (T (r,u))) := by
      filter_upwards [isOpen_Ioo.mem_nhds h₀I] with r hr
      have HE := chartGeodesicEnergy_constant h hh c (fun s => ζ (r,s)) (hs r hr) h₀J hu
      simpa only [chartGeodesicEnergy,hi r hr] using HE
    have HE := (H.congr_of_eventuallyEq hEq).unique (fixedMetric_velocityQuadratic_hasDerivAt h c z v w)
    rw [chartChristoffelBilin_symm h c (Z (0,u)) (V u) (T (0,u))] at HE
    linarith
  have hP (u : ℝ) (hu : u ∈ J) :
      HasDerivAt (fun s => realMetricInChart h c (Z (0,s)) (T (0,s)) (V s))
        (realMetricInChart h c z v w) u := by
    have H := chartGeodesic_pairing_hasDerivAt h hh c
      (z := fun s => Z (0,s)) (T := fun s => T (0,s)) (J := V) (t := u) (J' := W u)
      (hs 0 h₀I u hu).1
      (hZtime u hu) (hTtime u hu) (hVtime u hu)
    rw [henergy u hu] at H
    exact H
  have hPdiff (u : ℝ) (hu : u ∈ J) :
      HasDerivAt (fun s => realMetricInChart h c (Z (0,s)) (T (0,s)) (V s)-
        s*realMetricInChart h c z v w) 0 u := by
    convert! (hP u hu).sub ((hasDerivAt_id u).mul_const (realMetricInChart h c z v w)) using 1 <;> simp
  have hVzero : V 0 = 0 := by
    have H : (fun r => Z (r,0)) =ᶠ[𝓝 (0 : ℝ)] (fun _ => z) := by
      filter_upwards [isOpen_Ioo.mem_nhds h₀I] with r hr
      exact congrArg Prod.fst (hi r hr)
    exact H.deriv_eq.trans (deriv_const 0 z)
  have H := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-ε) (1+ε)).isPreconnected
    (fun u hu => (hPdiff u hu).differentiableAt.differentiableWithinAt)
    (fun u hu => (hPdiff u hu).deriv) ht h₀J
  have Hzero : realMetricInChart h c (Z (0,t)) (T (0,t)) (V t)-
      t*realMetricInChart h c z v w = 0 := by
    simpa only [hVzero,map_zero,zero_mul,sub_zero] using H
  exact sub_eq_zero.mp Hzero

end Yau.LeafProofs.L23Aux
