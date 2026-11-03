import Yau.Proofs.D02PullbackRegularity

/-! The actual physical parameter derivative, in the actual pullback atlas. -/

open scoped Manifold Topology ContDiff Matrix Bundle ENNReal
open Bundle MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n} {B : ComplexManifold 1}

theorem tangentPullback_coordinates
    (f : ContMDiffMap (ComplexModel 1) (ComplexModel n) B.Carrier M.Carrier ⊤)
    (a x : B.Carrier)
    (hx : f x ∈ (extChartAt (ComplexModel n) (f a)).source)
    (v : tangentPullbackFiber f x) :
    (BundleDbar.localTriv (r := n) (tangentPullbackFiber f) a).continuousLinearMapAt ℂ x v =
      tangentCoords (f a) (f x) v := by
  let e := BundleDbar.localTriv (r := n) (tangentPullbackFiber f) a
  have hb : x ∈ e.baseSet := by
    change f x ∈ (chartAt (ComplexVector n) (f a)).source
    simpa only [extChartAt_source, Set.mem_preimage] using hx
  have h := congrArg (tangentCoords (f a) (f x))
    (e.symmL_continuousLinearMapAt (R := ℂ) hb v)
  rw [tangentPullback_frame f a x hx, tangentCoords_chartVec (f a) (f x) hx] at h
  exact h

def puncturedCurveMap (h : ℂ → M.Carrier)
    (hh : MDifferentiableOn 𝓘(ℂ, ℂ) (ComplexModel n) h puncturedUnitDisc)
    (c : BundlePresentation.DiscCoordinate B) (hc : BundlePresentation.IsDiscCoordinate c) :
    ContMDiffMap (ComplexModel 1) (ComplexModel n) B.Carrier M.Carrier ⊤ :=
  holomorphicCurveMap (fun x => h (c x)) (fun x =>
    (hh.mdifferentiableAt (Yau.Proofs.B01Aux.puncturedUnitDisc_isOpen.mem_nhds
      (Yau.Proofs.B01Aux.disc_mem c hc x))).comp x
        (hc.2.2.1.mdifferentiable (by simp) x))

def puncturedDerivativeSection (h : ℂ → M.Carrier)
    (hh : MDifferentiableOn 𝓘(ℂ, ℂ) (ComplexModel n) h puncturedUnitDisc)
    (c : BundlePresentation.DiscCoordinate B) (hc : BundlePresentation.IsDiscCoordinate c) :
    BundlePresentation.Section (tangentPullbackFiber (puncturedCurveMap h hh c hc)) :=
  physicalDerivativeSection h c

def puncturedCoordinateDomain (h : ℂ → M.Carrier) (y : M.Carrier) : Set ℂ :=
  puncturedUnitDisc ∩ h ⁻¹' (extChartAt (ComplexModel n) y).source

theorem puncturedCoordinateDomain_isOpen (h : ℂ → M.Carrier)
    (hh : MDifferentiableOn 𝓘(ℂ, ℂ) (ComplexModel n) h puncturedUnitDisc) (y : M.Carrier) :
    IsOpen (puncturedCoordinateDomain h y) :=
  hh.continuousOn.isOpen_inter_preimage Yau.Proofs.B01Aux.puncturedUnitDisc_isOpen
    (isOpen_extChartAt_source (I := ComplexModel n) y)

theorem puncturedCoordinate_differentiableOn (h : ℂ → M.Carrier)
    (hh : MDifferentiableOn 𝓘(ℂ, ℂ) (ComplexModel n) h puncturedUnitDisc) (y : M.Carrier) :
    DifferentiableOn ℂ (chartPt y ∘ h) (puncturedCoordinateDomain h y) := by
  have hi := hh.mono (show puncturedCoordinateDomain h y ⊆ puncturedUnitDisc from
    fun _ hz => hz.1)
  have hc := (mdifferentiableOn_extChartAt (I := ComplexModel n) (x := y)).comp hi
    (fun z hz => (show h z ∈ (chartAt (ComplexVector n) y).source from
      by simpa only [extChartAt_source, Set.mem_preimage] using hz.2))
  exact hc.differentiableOn

theorem puncturedCoordinate_fderiv_apply (h : ℂ → M.Carrier)
    (hh : MDifferentiableOn 𝓘(ℂ, ℂ) (ComplexModel n) h puncturedUnitDisc) (y : M.Carrier)
    {w : ℂ} (hw : w ∈ puncturedCoordinateDomain h y) :
    fderiv ℂ (chartPt y ∘ h) w 1 = tangentCoords y (h w)
      (mfderiv 𝓘(ℂ, ℂ) (ComplexModel n) h w
        ((tangentSpaceCastModel 𝓘(ℂ, ℂ) w).symm 1)) := by
  have hh' := hh.mdifferentiableAt (Yau.Proofs.B01Aux.puncturedUnitDisc_isOpen.mem_nhds hw.1)
  have hy : h w ∈ (chartAt (ComplexVector n) y).source := by
    simpa only [extChartAt_source, Set.mem_preimage] using hw.2
  have hc := mfderiv_comp_apply w (mdifferentiableAt_extChartAt (I := ComplexModel n) hy) hh'
    ((tangentSpaceCastModel 𝓘(ℂ, ℂ) w).symm 1)
  rw [mfderiv_eq_fderiv] at hc
  exact hc

theorem puncturedDerivativeSection_holomorphic (h : ℂ → M.Carrier)
    (hh : MDifferentiableOn 𝓘(ℂ, ℂ) (ComplexModel n) h puncturedUnitDisc)
    (c : BundlePresentation.DiscCoordinate B) (hc : BundlePresentation.IsDiscCoordinate c) :
    BundlePresentation.HolomorphicSection (r := n)
      (tangentPullbackFiber (puncturedCurveMap h hh c hc)) (puncturedDerivativeSection h hh c hc) := by
  intro a
  let f := puncturedCurveMap h hh c hc
  let U := BundleDbar.localDomain (r := n) (tangentPullbackFiber f) a
  have hmaps : Set.MapsTo (fun z => c (chartInv a z)) U
      (puncturedCoordinateDomain h (h (c a))) := by
    intro z hz
    refine ⟨Yau.Proofs.B01Aux.disc_mem c hc (chartInv a z), ?_⟩
    change f (chartInv a z) ∈ (extChartAt (ComplexModel n) (f a)).source
    have ht : f (chartInv a z) ∈ (chartAt (ComplexVector n) (f a)).source := hz.2
    simpa only [extChartAt_source, Set.mem_preimage] using ht
  have hc' : DifferentiableOn ℂ (fun z => c (chartInv a z)) U :=
    (((hc.2.2.1.mdifferentiable (by simp)).mdifferentiableOn :
      MDifferentiableOn (ComplexModel 1) 𝓘(ℂ, ℂ) c Set.univ).comp
      (((contMDiffOn_extChartAt_symm (I := ComplexModel 1) (n := ∞) a).mdifferentiableOn
        (by simp)).mono (show U ⊆ chartTarget a from fun _ hz => hz.1))
      (fun _ _ => Set.mem_univ _)).differentiableOn
  have hd := (complex_holomorphic_fderiv_apply_differentiableOn
    (puncturedCoordinateDomain_isOpen h hh (h (c a)))
    (puncturedCoordinate_differentiableOn h hh (h (c a))) (1 : ℂ)).comp hc' hmaps
  apply hd.congr
  intro z hz
  unfold BundlePresentation.sectionCoefficients
  have hvalid : f (chartInv a z) ∈ (extChartAt (ComplexModel n) (f a)).source := by
    have ht : f (chartInv a z) ∈ (chartAt (ComplexVector n) (f a)).source := hz.2
    simpa only [extChartAt_source, Set.mem_preimage] using ht
  rw [tangentPullback_coordinates f a (chartInv a z) hvalid]
  exact (puncturedCoordinate_fderiv_apply h hh (h (c a)) (hmaps hz)).symm

theorem puncturedDerivativeSection_integral (g : HermitianField M)
    (h : ℂ → M.Carrier)
    (hh : MDifferentiableOn 𝓘(ℂ, ℂ) (ComplexModel n) h puncturedUnitDisc)
    (c : BundlePresentation.DiscCoordinate B) (hc : BundlePresentation.IsDiscCoordinate c) :
    BundlePresentation.sectionIntegral (tangentPullbackFiber (puncturedCurveMap h hh c hc)) c
      (tangentPullbackMetric g (puncturedCurveMap h hh c hc))
      (puncturedDerivativeSection h hh c hc) =
      ∫⁻ z in puncturedUnitDisc, ENNReal.ofReal
        (hermitianNormSq (g (h z))
          (mfderiv 𝓘(ℂ, ℂ) (ComplexModel n) h z
            ((tangentSpaceCastModel 𝓘(ℂ, ℂ) z).symm 1))) ∂volume := by
  unfold BundlePresentation.sectionIntegral
  rw [Yau.Proofs.B01Aux.lintegral_discArea c hc]
  apply setLIntegral_congr_fun Yau.Proofs.B01Aux.puncturedUnitDisc_measurableSet
  intro z hz
  change ENNReal.ofReal (hermitianNormSq (g (h (c (c.symm z))))
    (mfderiv 𝓘(ℂ, ℂ) (ComplexModel n) h (c (c.symm z))
      ((tangentSpaceCastModel 𝓘(ℂ, ℂ) (c (c.symm z))).symm 1))) = _
  rw [Yau.Proofs.B01Aux.disc_right_inv c hc hz]

/-- The D03 weight is transported to ordinary physical planar area exactly. -/
theorem puncturedDerivativeSection_weightedIntegral (g : HermitianField M)
    (h : ℂ → M.Carrier)
    (hh : MDifferentiableOn 𝓘(ℂ, ℂ) (ComplexModel n) h puncturedUnitDisc)
    (c : BundlePresentation.DiscCoordinate B) (hc : BundlePresentation.IsDiscCoordinate c)
    (ρ σ : ℝ) (hρ : ρ ≤ 1) :
    BundlePresentation.weightedSectionIntegral
      (tangentPullbackFiber (puncturedCurveMap h hh c hc)) c
      (tangentPullbackMetric g (puncturedCurveMap h hh c hc))
      (puncturedDerivativeSection h hh c hc) ρ σ =
      ∫⁻ z in {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < ρ}, ENNReal.ofReal
        (hermitianNormSq (g (h z))
          (mfderiv 𝓘(ℂ, ℂ) (ComplexModel n) h z
            ((tangentSpaceCastModel 𝓘(ℂ, ℂ) z).symm 1)) * ‖z‖ ^ (-σ)) ∂volume := by
  have hS : MeasurableSet {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < ρ} :=
    ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)).measurableSet
  have hSD : {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < ρ} ⊆ puncturedUnitDisc :=
    fun z hz => ⟨hz.1, lt_of_lt_of_le hz.2 hρ⟩
  unfold BundlePresentation.weightedSectionIntegral
  change (∫⁻ x in c ⁻¹' {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < ρ},
    ENNReal.ofReal (hermitianNormSq
      (tangentPullbackMetric g (puncturedCurveMap h hh c hc) x)
      (puncturedDerivativeSection h hh c hc x) * ‖c x‖ ^ (-σ))
        ∂BundlePresentation.discArea c) = _
  rw [Yau.Proofs.B01Aux.setLIntegral_discArea c hc _ hS hSD]
  apply setLIntegral_congr_fun hS
  intro z hz
  change ENNReal.ofReal (hermitianNormSq (g (h (c (c.symm z))))
    (mfderiv 𝓘(ℂ, ℂ) (ComplexModel n) h (c (c.symm z))
      ((tangentSpaceCastModel 𝓘(ℂ, ℂ) (c (c.symm z))).symm 1)) *
        ‖c (c.symm z)‖ ^ (-σ)) = _
  rw [Yau.Proofs.B01Aux.disc_right_inv c hc (hSD hz)]

end Yau.NodeProofs.D02Aux
