import Yau.Proofs.P06ExteriorHeat
import Yau.Proofs.P06FormUniqueness
import Yau.Proofs.P06L2HeatExistence
import Yau.Proofs.P06TimeIntegralPotential

/-! Closedness and the original time-integral potential from the cutoff construction. -/
noncomputable section
open MeasureTheory
open scoped Topology

namespace Yau.NodeProofs.P06Aux.ClosedPotential
open Yau Yau.Blueprint Yau.LeafProofs.L03
variable {n : ℕ}

/-- The actual canonical cutoff limit is closed. Original bounded-PDE
uniqueness transfers this conclusion to every solution in the original class. -/
theorem boundedFormHeat_closed_of_cutoffConstruction
    (X : KahlerManifold n) (μ : Measure X.manifold.Carrier)
    (hμ : IsRiemannianVolume X.metric.form μ)
    (hc : HodgeCutoffConstruction X.metric.form μ)
    (A : RealForm X.manifold 2) (U : ℝ → RealForm X.manifold 2)
    (hA : BoundedOneOneData X.metric.form A) (hclosedA : ClosedRealForm A)
    (hU : IsBoundedFormHeat X.metric.form A U) :
    ∀ t, 0 < t → ClosedRealForm (U t) := by
  obtain ⟨V, hV, hcut⟩ := hc.2 A hA
  obtain ⟨o⟩ := (inferInstance : Nonempty X.manifold.Carrier)
  obtain ⟨χ, hχ⟩ := hc.1 o
  obtain ⟨hcutL2, ⟨Us, hUs⟩, hlimit⟩ := hcut o χ hχ
  have hUsL2 : ∀ j, 1 ≤ j → ∀ t, 0 < t → L2RealForm X.metric.form μ (Us j t) :=
    fun j hj t ht => (hUs j hj).2.2.2.2.1 t ht
  have hrep : ∀ j (hj : 1 ≤ j) t (ht : 0 < t),
      realizeActualForm X.metric μ (Us j t) (hUsL2 j hj t ht) =
        hodgeHeatHilbert X.metric μ hμ 2 t
          (ExteriorHeat.cutoffVector X.metric μ hμ o χ hχ A hA.1 j hj) := by
    intro j hj t ht
    exact L2HeatExistence.isL2FormHeat_realization X.metric μ hμ
      (fun x => χ j x • A x) (hcutL2 j hj) (Us j) (hUs j hj) ht
  have hclosedV := ExteriorHeat.canonical_cutoff_localSmoothLimit_closed X μ hμ A hA hclosedA
    o χ hχ Us V hUsL2 hrep (fun t ht => smoothFormTime_slice hV.1 ht) (hlimit Us hUs)
  intro t ht
  rw [boundedFormHeat_unique X A U V hU hV t ht.le]
  exact hclosedV t ht

/-- The cutoff construction is an internal input. The conclusion is the
unchanged closed-potential target for every original bounded form/scalar heat. -/
theorem closedPotential_of_cutoffConstruction
    (X : KahlerManifold n) (μ : Measure X.manifold.Carrier)
    (hμ : IsRiemannianVolume X.metric.form μ)
    (hc : HodgeCutoffConstruction X.metric.form μ) : HodgeClosedPotential X.metric.form := by
  intro A U u hA hclosedA hU hu t ht
  have hclosed := boundedFormHeat_closed_of_cutoffConstruction X μ hμ hc A U hA hclosedA hU
  exact ⟨hclosed t ht, TimePotential.boundedFormHeat_timeIntegralPotential X hA hU hu hclosed ht⟩

end Yau.NodeProofs.P06Aux.ClosedPotential
