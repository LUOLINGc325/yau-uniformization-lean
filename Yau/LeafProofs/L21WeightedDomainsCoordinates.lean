import Yau.LeafProofs.L21WeightedDomainsTests

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.LeafProofs.L21Aux

abbrev WeightedField (n : ℕ) (K : ℝ) (ι : Type*) [Fintype ι] :=
  Lp (EuclideanSpace ℂ ι) 2 (weightedBallMeasure n K)

def weightedFieldProjection {n : ℕ} (K : ℝ) {ι : Type*} [Fintype ι] (i : ι) :
    WeightedField n K ι →L[ℂ] WeightedScalar n K :=
  (EuclideanSpace.proj i : EuclideanSpace ℂ ι →L[ℂ] ℂ).compLpL 2 (weightedBallMeasure n K)

theorem weightedFieldProjection_coeFn {n : ℕ} (K : ℝ) {ι : Type*} [Fintype ι]
    (i : ι) (u : WeightedField n K ι) :
    (weightedFieldProjection K i u : X n → ℂ) =ᵐ[weightedBallMeasure n K] (fun x => u x i) :=
  (EuclideanSpace.proj i : EuclideanSpace ℂ ι →L[ℂ] ℂ).coeFn_compLpL u

theorem weightedField_eq_zero_of_projections {n : ℕ} (K : ℝ) {ι : Type*} [Fintype ι]
    (u : WeightedField n K ι) (hZero : ∀ i, weightedFieldProjection K i u = 0) : u = 0 := by
  have hRaw (i : ι) : ∀ᵐ x ∂weightedBallMeasure n K, u x i = 0 := by
    have hh := weightedFieldProjection_coeFn K i u
    rw [hZero i] at hh
    filter_upwards [hh,Lp.coeFn_zero (E := ℂ) (p := 2) (μ := weightedBallMeasure n K)] with x hx hz
    exact hx.symm.trans hz
  apply Lp.ext
  filter_upwards [ae_all_iff.mpr hRaw,
    Lp.coeFn_zero (E := EuclideanSpace ℂ ι) (p := 2) (μ := weightedBallMeasure n K)] with x hx hz
  have he : u x = 0 := by ext i; exact hx i
  exact he.trans hz.symm

theorem weightedField_compactFunctional_apply {n : ℕ} (K : ℝ) (hK : 0 ≤ K)
    {ι : Type*} [Fintype ι] (i : ι) (u : WeightedField n K ι)
    (ψ : CompactTest (Metric.ball (0 : X n) 1)) :
    weightedCompactFunctional K hK ψ (weightedFieldProjection K i u) =
      ∫ x, ψ x*u x i ∂Yau.lebesgueC n :=
  weightedCompactFunctional_apply_representative K hK ψ _ (weightedFieldProjection_coeFn K i u).symm

theorem weightedField_eq_zero_of_compact_functionals {n : ℕ} (K : ℝ) (hK : 0 ≤ K)
    {ι : Type*} [Fintype ι] (u : WeightedField n K ι)
    (hZero : ∀ i (ψ : CompactTest (Metric.ball (0 : X n) 1)),
      weightedCompactFunctional K hK ψ (weightedFieldProjection K i u) = 0) : u = 0 := by
  apply weightedField_eq_zero_of_projections K u
  intro i
  exact weightedCompactFunctional_separates K hK _ (hZero i)

end Yau.LeafProofs.L21Aux
