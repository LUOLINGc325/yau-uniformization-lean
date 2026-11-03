import Yau.Proofs.P04CanonicalCompatibility

noncomputable section
open Set Filter MeasureTheory Bundle
open scoped Topology Manifold ContDiff

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

def gluedCanonicalTop (f : M.Carrier → ComplexVector n → ℂ) :
    BundleDbar.NQForm (CanonicalCoefficients M) 0 := fun x => localCanonicalTop x (f x) x

theorem gluedCanonicalTop_eq_local (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (u : BundleDbar.NQForm (CanonicalCoefficients M) 0)
    (f : M.Carrier → ComplexVector n → ℂ)
    (hf : ∀ a, DifferentiableOn ℂ (f a) (chartTarget a))
    (hae : ∀ a, (fun z => BundleDbar.coefficients (r := 1) (CanonicalCoefficients M) u a z Fin.elim0 0)
      =ᵐ[(lebesgueC n).restrict (chartTarget a)] f a)
    (a x : M.Carrier) (hx : x ∈ (extChartAt (ComplexModel n) a).source) :
    gluedCanonicalTop f x=localCanonicalTop a (f a) x :=
  localCanonicalTop_compatible g μ hμ x a u (f x) (f a) (hf x) (hf a) (hae x) (hae a)
    (mem_extChartAt_source x) hx

/-- The local CR representatives glue into a genuine holomorphic top tensor.
The final AE assertion uses a countable chart subcover, not an intersection
over the uncountable chart index. -/
theorem glue_canonical_coefficients (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (u : BundleDbar.NQForm (CanonicalCoefficients M) 0)
    (f : M.Carrier → ComplexVector n → ℂ)
    (hf : ∀ a, DifferentiableOn ℂ (f a) (chartTarget a))
    (hae : ∀ a, (fun z => BundleDbar.coefficients (r := 1) (CanonicalCoefficients M) u a z Fin.elim0 0)
      =ᵐ[(lebesgueC n).restrict (chartTarget a)] f a) :
    ∃ v : BundleDbar.NQForm (CanonicalCoefficients M) 0,
      BundleDbar.HolomorphicTopForm (r := 1) (CanonicalCoefficients M) v ∧ ∀ᵐ x ∂μ, u x=v x := by
  refine ⟨gluedCanonicalTop f,?_,?_⟩
  · intro a α
    have hα : α=(0 : Fin 1) := Subsingleton.elim _ _
    subst α
    rw [coefficient_localDomain]
    apply (hf a).congr
    intro z hz
    have hx : chartInv a z ∈ (extChartAt (ComplexModel n) a).source :=
      (extChartAt (ComplexModel n) a).map_target hz
    have heq := gluedCanonicalTop_eq_local g μ hμ u f hf hae a (chartInv a z) hx
    calc
      _ = BundleDbar.coefficients (r := 1) (CanonicalCoefficients M)
          (localCanonicalTop a (f a)) a z Fin.elim0 0 := by
        unfold BundleDbar.coefficients
        rw [heq]
      _ = _ := localCanonicalTop_coefficient a (f a) hz
  · have hlocal (a : M.Carrier) :
        ∀ᵐ x ∂μ.restrict ((extChartAt (ComplexModel n) a).source), u x=gluedCanonicalTop f x := by
      filter_upwards [localCanonicalTop_ae_on_chart g μ hμ a u (f a) (hae a),
        ae_restrict_mem (isOpen_extChartAt_source a).measurableSet] with x hux hx
      exact hux.trans (gluedCanonicalTop_eq_local g μ hμ u f hf hae a x hx).symm
    obtain ⟨a,ha⟩ := isLindelof_univ.indexed_countable_subcover
      (fun a : M.Carrier => (extChartAt (ComplexModel n) a).source)
      (fun a => isOpen_extChartAt_source a)
      (by intro x _; exact mem_iUnion.mpr ⟨x,mem_extChartAt_source x⟩)
    have hcover : (⋃ j, (extChartAt (ComplexModel n) (a j)).source)=univ :=
      eq_univ_of_univ_subset ha
    have H : ∀ᵐ x ∂μ.restrict (⋃ j, (extChartAt (ComplexModel n) (a j)).source),
        u x=gluedCanonicalTop f x :=
      (ae_restrict_iUnion_iff _ _).mpr (fun j => hlocal (a j))
    simpa only [hcover,Measure.restrict_univ] using H

end Yau.Proofs.P04Aux
