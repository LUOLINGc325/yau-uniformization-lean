import Yau.Proofs.G02DensityTransition

noncomputable section
open MeasureTheory
open scoped Topology Manifold ENNReal Matrix ContDiff

namespace Yau.Proofs.G02Aux
open Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

theorem chart_image_overlap (a b : M.Carrier) {s : Set M.Carrier}
    (hsa : s ⊆ chartSource a) (hsb : s ⊆ chartSource b)
    {z : ComplexVector n} (hz : z ∈ chartPt a '' s) :
    z ∈ chartTarget a ∧ chartInv a z ∈ chartSource b := by
  obtain ⟨p, hp, rfl⟩ := hz
  refine ⟨(extChartAt (ComplexModel n) a).map_source (hsa hp), ?_⟩
  rw [show chartInv a (chartPt a p) = p from
    (extChartAt (ComplexModel n) a).left_inv (hsa hp)]
  exact hsb hp

theorem chart_transition_image (a b : M.Carrier) (s : Set M.Carrier)
    (hsa : s ⊆ chartSource a) :
    L12Aux.realChartChange a b '' (chartPt a '' s) = chartPt b '' s := by
  ext z
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    refine ⟨p, hp, ?_⟩
    change chartPt b p = chartPt b (chartInv a (chartPt a p))
    rw [show chartInv a (chartPt a p) = p from
      (extChartAt (ComplexModel n) a).left_inv (hsa hp)]
  · rintro ⟨p, hp, rfl⟩
    refine ⟨chartPt a p, ⟨p, hp, rfl⟩, ?_⟩
    change chartPt b (chartInv a (chartPt a p)) = chartPt b p
    rw [show chartInv a (chartPt a p) = p from
      (extChartAt (ComplexModel n) a).left_inv (hsa hp)]

theorem chart_transition_injOn (a b : M.Carrier) :
    Set.InjOn (L12Aux.realChartChange a b)
      {z | z ∈ chartTarget a ∧ chartInv a z ∈ chartSource b} := by
  intro z hz w hw he
  have hi := congrArg (L12Aux.realChartChange b a) he
  rwa [L12Aux.realChartChange_inverse_apply a b hz.1 hz.2,
    L12Aux.realChartChange_inverse_apply a b hw.1 hw.2] at hi

theorem chart_transition_hasFDerivWithinAt (a b : M.Carrier)
    {s : Set (ComplexVector n)} {z : ComplexVector n}
    (hza : z ∈ chartTarget a) (hzb : chartInv a z ∈ chartSource b) :
    HasFDerivWithinAt (L12Aux.realChartChange a b)
      (fderiv ℝ (L12Aux.realChartChange a b) z) s z :=
  ((L12Aux.realChartChange_contDiffAt a b hza hzb).differentiableAt
    (by simp)).hasFDerivAt.hasFDerivWithinAt

theorem chart_density_integral_eq (h : HermitianField M) (a b : M.Carrier)
    (s : Set M.Carrier) (hs : MeasurableSet s)
    (hsa : s ⊆ chartSource a) (hsb : s ⊆ chartSource b) :
    (∫⁻ z in chartPt a '' s, density h a z ∂lebesgueC n) =
      ∫⁻ z in chartPt b '' s, density h b z ∂lebesgueC n := by
  let A : Set (ComplexVector n) := chartPt a '' s
  let F : ComplexVector n → ComplexVector n := L12Aux.realChartChange a b
  have hA : MeasurableSet A := measurableSet_chart_image a s hs hsa
  have hmem : ∀ z ∈ A,
      z ∈ chartTarget a ∧ chartInv a z ∈ chartSource b :=
    fun _ hz => chart_image_overlap a b hsa hsb hz
  have hder : ∀ z ∈ A, HasFDerivWithinAt F (fderiv ℝ F z) A z := by
    intro z hz
    exact chart_transition_hasFDerivWithinAt a b (hmem z hz).1 (hmem z hz).2
  have hinj : Set.InjOn F A :=
    (chart_transition_injOn a b).mono (fun z hz => hmem z hz)
  have himage : F '' A = chartPt b '' s := chart_transition_image a b s hsa
  have hjac := lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (volume : Measure (ComplexVector n)) hA hder hinj (density h b)
  rw [himage] at hjac
  have hrho :
      (∫⁻ z in A, ENNReal.ofReal |(fderiv ℝ F z).det| * density h b (F z)
        ∂(volume : Measure (ComplexVector n))) =
      ∫⁻ z in A, density h a z ∂(volume : Measure (ComplexVector n)) := by
    apply setLIntegral_congr_fun hA
    intro z hz
    exact (density_transition h a b (hmem z hz).1 (hmem z hz).2).symm
  simpa only [lebesgueC_eq_volume, A] using (hjac.trans hrho).symm

theorem localVolume_eq_on_overlap (h : HermitianField M) (a b : M.Carrier)
    (s : Set M.Carrier) (hs : MeasurableSet s)
    (hsa : s ⊆ chartSource a) (hsb : s ⊆ chartSource b) :
    localVolume h a s = localVolume h b s := by
  rw [localVolume_apply_of_subset h a s hs hsa,
    localVolume_apply_of_subset h b s hs hsb]
  exact chart_density_integral_eq h a b s hs hsa hsb

end Yau.Proofs.G02Aux
