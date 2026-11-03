import Yau.LeafProofs.L05AutonomousPeanoMeasurableBounds
import Mathlib.MeasureTheory.Measure.Prod

noncomputable section
open Filter Set MeasureTheory Asymptotics
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- A concrete canonical dyadic Hessian and a measurable full-measure good set
are constructed from the literal slice Peano and actual finite-difference data. -/
theorem peano_measurable_hessian (n : ℕ) :
   ∃ C : ℝ, 0 < C ∧
   ∀ (O : Set (Space n)), IsOpen O →
   ∀ (I : Set ℝ), MeasurableSet I →
   ∀ M h0 : ℝ, 0 ≤ M → 0 < h0 →
   ∀ (u : Point n → ℝ), Continuous u →
   ∀ (G : Point n → (Space n →L[ℝ] ℝ)), Measurable G →
   (∀ t ∈ I, ∀ᵐ x ∂((volume : Measure (Space n)).restrict O),
     ∃ B : Space n →L[ℝ] Space n →L[ℝ] ℝ,
       (∀ v w, B v w=B w v) ∧
       (fun y => u (y,t)-u (x,t)-G (x,t) (y-x)-
         (1/2 : ℝ)*B (y-x) (y-x))
           =o[𝓝 x] (fun y => ‖y-x‖^2)) →
   (∀ e : Space n, ‖e‖=1 → ∀ h : ℝ, h ≠ 0 → |h| < h0 →
     ∀ p ∈ O ×ˢ I, |autoSecond u e h p| ≤ M) →
   Measurable (peanoMeasurableHessian u) ∧
   ∃ S : Set (Point n), MeasurableSet S ∧ S ⊆ O ×ˢ I ∧
     (∀ᵐ p ∂((volume : Measure (Point n)).restrict (O ×ˢ I)), p ∈ S) ∧
     (∀ p ∈ S,
       (fun y => u (y,p.2)-u p-G p (y-p.1)-
         (1/2 : ℝ)*autoBilinearMap n (peanoMeasurableHessian u p) (y-p.1) (y-p.1))
           =o[𝓝 p.1] (fun y => ‖y-p.1‖^2)) ∧
     (∀ p ∈ S, ‖peanoMeasurableHessian u p‖ ≤ C*M) ∧
     (∀ p ∈ S, ∀ e : Space n,
       Tendsto (fun h => autoSecond u e h p) (𝓝[>] 0)
         (𝓝 (autoBilinearMap n (peanoMeasurableHessian u p) e e))) := by
  refine ⟨4*(n : ℝ)+1,by positivity,?_⟩
  intro O hO I hI M h0 hM hh0 u hu G hG hSlice hFinite
  let S : Set (Point n) := (O ×ˢ I) ∩ peanoCountableGoodSet u G
  have hS : MeasurableSet S :=
    (hO.measurableSet.prod hI).inter (measurableSet_peanoCountableGoodSet hu hG)
  have hPerTime : ∀ t ∈ I, ∀ᵐ x ∂((volume : Measure (Space n)).restrict O), (x,t) ∈ S := by
    intro t ht
    filter_upwards [hSlice t ht,ae_restrict_mem hO.measurableSet] with x hx hxO
    obtain ⟨B,hB,hRem⟩ := hx
    refine ⟨⟨hxO,ht⟩,?_⟩
    apply peano_countable_of_littleO
    have hIdentity : autoBilinearMap n (peanoMeasurableHessian u (x,t))=B :=
      peanoMeasurableHessian_bilinear_of_peano (u := u) (p := (x,t))
        (l := G (x,t)) (B := B) hB hRem
    simpa only [hIdentity] using hRem
  have hTimeSpace : ∀ᵐ t ∂((volume : Measure ℝ).restrict I),
      ∀ᵐ x ∂((volume : Measure (Space n)).restrict O), (x,t) ∈ S := by
    filter_upwards [ae_restrict_mem hI] with t ht
    exact hPerTime t ht
  have hSpaceTime : ∀ᵐ x ∂((volume : Measure (Space n)).restrict O),
      ∀ᵐ t ∂((volume : Measure ℝ).restrict I), (x,t) ∈ S :=
    (Measure.ae_ae_comm (p := fun (x : Space n) (t : ℝ) => (x,t) ∈ S) hS).mpr hTimeSpace
  have hProduct : ∀ᵐ p ∂(((volume : Measure (Space n)).restrict O).prod
      ((volume : Measure ℝ).restrict I)), p ∈ S :=
    (Measure.ae_prod_mem_iff_ae_ae_mem hS).mpr hSpaceTime
  have hFull : ∀ᵐ p ∂((volume : Measure (Point n)).restrict (O ×ˢ I)), p ∈ S := by
    simpa only [Measure.prod_restrict,← Measure.volume_eq_prod] using hProduct
  refine ⟨measurable_peanoMeasurableHessian hu,S,hS,inter_subset_left,hFull,?_,?_,?_⟩
  · intro p hp
    exact peano_littleO_of_countable hu hp.2
  · intro p hp
    exact peano_good_hessian_bound hu hM hh0 hFinite hp.1 hp.2
  · intro p hp e
    exact peano_second_limit (peano_littleO_of_countable hu hp.2) e

end Yau.LeafProofs.L05AutonomousAux
