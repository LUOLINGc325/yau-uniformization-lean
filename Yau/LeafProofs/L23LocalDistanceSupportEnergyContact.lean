import Yau.LeafProofs.L23LocalDistanceSupportEnergyAdmissible
import Yau.LeafProofs.L23LocalDistanceSupportEnergySmooth

/-! Actual endpoint-variation energies dominate squared distance and touch on the minimizing path. -/
noncomputable section
open Filter MeasureTheory
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1000000

theorem endpointVariation_fiber_contMDiffOn_three
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (A : ℝ → ComplexVector n → M.Carrier) (J : Set ℝ) :
    letI := manifold_realSmooth M
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry A) (J ×ˢ e.source) →
    ∀ v ∈ e.source, ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 3 (fun u => A u v) J := by
  letI := manifold_realSmooth M
  intro hA v hv
  have HM : ContDiffOn ℝ 3 (fun u : ℝ => (u,v)) J := contDiffOn_id.prodMk contDiffOn_const
  have HMm : ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 3 (fun u : ℝ => (u,v)) J :=
    HM.fst.contMDiffOn.prodMk HM.snd.contMDiffOn
  exact hA.comp HMm (fun u hu => ⟨hu,hv⟩)

theorem endpointVariation_inducedDistance_sq_le_energy
    (h : HermitianField M) (hh : MetricSmooth h) (q : M.Carrier)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (A : ℝ → ComplexVector n → M.Carrier) (δ : ℝ) (hδ : 0 < δ)
    (hend : ∀ v ∈ e.source, A 0 v = q ∧ A 1 v = e v) :
    letI := manifold_realSmooth M
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry A) (Set.Ioo (-δ) (1+δ) ×ˢ e.source) →
    ∀ z ∈ e.target, inducedDistance h q z ^ 2 ≤
      fieldPathEnergy h (fun u => A u (e.symm z)) := by
  letI := manifold_realSmooth M
  intro hA z hz
  have hv : e.symm z ∈ e.source := e.map_target hz
  have Hcurve := (endpointVariation_fiber_contMDiffOn_three e A _ hA (e.symm z) hv).of_le (by norm_num : (1 : ℕ∞ω) ≤ 3)
  have H := inducedDistance_sq_le_fieldPathEnergy_of_contMDiffOn h hh (fun u => A u (e.symm z)) δ hδ Hcurve
  rw [(hend _ hv).1,(hend _ hv).2,e.right_inv hz] at H
  exact H

theorem endpointVariation_fieldPathEnergy_contact
    (h : HermitianField M) (γ : ℝ → M.Carrier)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (A : ℝ → ComplexVector n → M.Carrier) (δ : ℝ) (hδ : 0 < δ)
    (hzero : (0 : ComplexVector n) ∈ e.source) (he0 : e 0 = γ 1)
    (hA0 : ∀ u ∈ Set.Ioo (-δ) (1+δ), A u 0 = γ u)
    (D : ℝ) (hspeed : ∀ u ∈ Set.Icc (0 : ℝ) 1, actualSpeedSq h γ u = D) :
    letI := manifold_realSmooth M
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry A) (Set.Ioo (-δ) (1+δ) ×ˢ e.source) →
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 γ (Set.Ioo (-δ) (1+δ)) →
    fieldPathEnergy h (fun u => A u (e.symm (γ 1))) = D := by
  letI := manifold_realSmooth M
  intro hA hγ
  have hinv : e.symm (γ 1) = 0 := by rw [← he0]; exact e.left_inv hzero
  rw [hinv]
  have Hcurve := (endpointVariation_fiber_contMDiffOn_three e A _ hA 0 hzero).of_le (by norm_num : (1 : ℕ∞ω) ≤ 3)
  have HE := fieldPathEnergy_congr_on_open h (fun u => A u 0) γ _ isOpen_Ioo
    (by intro u hu; constructor <;> linarith [hu.1,hu.2]) hA0 Hcurve hγ
  exact HE.trans (fieldPathEnergy_eq_of_constant_actualSpeedSq h γ D hspeed)

end Yau.LeafProofs.L23Aux
