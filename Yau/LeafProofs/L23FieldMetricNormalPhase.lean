import Yau.LeafProofs.L23FieldMetricLocalNormal

/-! The velocity of a genuine C3 normal position family is an actual joint C2 spray family. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 600000

def normalFamilyPhase
    (X : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n)
    (p : ComplexVector n × ComplexVector n) (u : ℝ) : ComplexVector n × ComplexVector n :=
  (X p u,fderiv ℝ (Function.uncurry X) (p,u) (0,1))

theorem normalFamilyPhase_contDiffOn
    (X : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n)
    {D : Set (ComplexVector n × ComplexVector n)} {J : Set ℝ}
    (hD : IsOpen D) (hJ : IsOpen J)
    (hX : ContDiffOn ℝ 3 (Function.uncurry X) (D ×ˢ J)) :
    ContDiffOn ℝ 2 (Function.uncurry (normalFamilyPhase X)) (D ×ˢ J) := by
  exact (hX.of_le (by norm_num)).prodMk
    ((hX.fderiv_of_isOpen (hD.prod hJ) (m := 2) (by norm_num)).clm_apply contDiffOn_const)

theorem normalFamilyPhase_second_eq_deriv
    (X : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n)
    {p : ComplexVector n × ComplexVector n} {u : ℝ}
    (hX : DifferentiableAt ℝ (Function.uncurry X) (p,u)) :
    (normalFamilyPhase X p u).2 = deriv (X p) u := by
  have H := hX.hasFDerivAt.comp_hasDerivAt u
    ((hasDerivAt_const u p).prodMk (hasDerivAt_id u))
  exact H.deriv.symm

theorem geoChartState_normalFamilyPhase
    (c : M.Carrier) (X : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n)
    {D : Set (ComplexVector n × ComplexVector n)} {J : Set ℝ}
    (hD : IsOpen D) (hJ : IsOpen J)
    (hX : ContDiffOn ℝ 3 (Function.uncurry X) (D ×ˢ J))
    (htarget : ∀ p ∈ D, ∀ u ∈ J, X p u ∈ chartTarget c)
    (p : ComplexVector n × ComplexVector n) (hp : p ∈ D) (u : ℝ) (hu : u ∈ J) :
    geoChartState (fun s => chartInv c (X p s)) c u = normalFamilyPhase X p u := by
  have hcoord : (fun s => chartPt c (chartInv c (X p s))) =ᶠ[𝓝 u] X p := by
    filter_upwards [hJ.mem_nhds hu] with s hs
    exact (extChartAt (ComplexModel n) c).right_inv (htarget p hp s hs)
  have Hdiff : DifferentiableAt ℝ (Function.uncurry X) (p,u) :=
    (hX.contDiffAt ((hD.prod hJ).mem_nhds ⟨hp,hu⟩)).differentiableAt (by norm_num)
  unfold geoChartState
  apply Prod.ext
  · exact hcoord.self_of_nhds
  · exact hcoord.deriv_eq.trans (normalFamilyPhase_second_eq_deriv X Hdiff).symm

theorem normalFamilyPhase_is_solution
    (h : HermitianField M) (c : M.Carrier)
    (X : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n)
    {D : Set (ComplexVector n × ComplexVector n)} {J : Set ℝ}
    (hD : IsOpen D) (hJ : IsOpen J)
    (hX : ContDiffOn ℝ 3 (Function.uncurry X) (D ×ˢ J))
    (htarget : ∀ p ∈ D, ∀ u ∈ J, X p u ∈ chartTarget c)
    (hgeo : ∀ p ∈ D, FieldGeodesicOn h (fun s => chartInv c (X p s)) J)
    (p : ComplexVector n × ComplexVector n) (hp : p ∈ D) (u : ℝ) (hu : u ∈ J) :
    HasDerivAt (normalFamilyPhase X p)
      (chartGeodesicSpray h c (normalFamilyPhase X p u)) u := by
  have hsource : chartInv c (X p u) ∈ (extChartAt (ComplexModel n) c).source :=
    (extChartAt (ComplexModel n) c).map_target (htarget p hp u hu)
  have H := (hgeo p hp).2 c u hu hsource
  have hEq : normalFamilyPhase X p =ᶠ[𝓝 u]
      geoChartState (fun s => chartInv c (X p s)) c := by
    filter_upwards [hJ.mem_nhds hu] with s hs
    exact (geoChartState_normalFamilyPhase c X hD hJ hX htarget p hp s hs).symm
  rw [← hEq.self_of_nhds] at H
  exact H.congr_of_eventuallyEq hEq

theorem normalFamilyPhase_initial
    (X : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n)
    {D : Set (ComplexVector n × ComplexVector n)} {J : Set ℝ}
    (hD : IsOpen D) (hJ : IsOpen J) (h₀ : (0 : ℝ) ∈ J)
    (hX : ContDiffOn ℝ 3 (Function.uncurry X) (D ×ˢ J))
    (hi : ∀ p ∈ D, X p 0 = p.1 ∧ deriv (X p) 0 = p.2)
    (p : ComplexVector n × ComplexVector n) (hp : p ∈ D) : normalFamilyPhase X p 0 = p := by
  have Hdiff : DifferentiableAt ℝ (Function.uncurry X) (p,0) :=
    (hX.contDiffAt ((hD.prod hJ).mem_nhds ⟨hp,h₀⟩)).differentiableAt (by norm_num)
  exact Prod.ext (hi p hp).1 ((normalFamilyPhase_second_eq_deriv X Hdiff).trans (hi p hp).2)

end Yau.LeafProofs.L23Aux
