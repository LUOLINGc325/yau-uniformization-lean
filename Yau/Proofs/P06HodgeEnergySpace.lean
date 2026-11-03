import Yau.Proofs.P06GraphEnergy
import Mathlib.Analysis.InnerProductSpace.ProdL2

noncomputable section
open MeasureTheory
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

abbrev HodgeEnergyAmbient (g : SmoothMetric M) (μ : Measure M.Carrier) :=
  WithLp 2 (L2FormHilbert g μ 2 × WithLp 2 (L2FormHilbert g μ 3 × L2FormHilbert g μ 1))

def hodgeEnergyCoreTuple (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M 2)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) : HodgeEnergyAmbient g μ :=
  WithLp.toLp 2
    (realizeActualForm g μ A (smooth_compactlySupported_l2RealForm g μ hμ A hA hcA),
      WithLp.toLp 2
        (realizeActualForm g μ (exteriorRealForm A) (exteriorRealForm_l2 g μ hμ A hA hcA),
          realizeActualForm g μ (codifferentialRealForm g.form A)
            (codifferentialRealForm_l2 g μ hμ A hA hcA)))

def hodgeEnergyCoreSet (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) : Set (HodgeEnergyAmbient g μ) :=
  {p | ∃ A : RealForm M 2, ∃ hA : SmoothRealForm A, ∃ hcA : CompactlySupportedRealForm A,
    p = hodgeEnergyCoreTuple g μ hμ A hA hcA}

/-- The closed real span of the actual compact smooth (A,dA,δA) triples,
inside the genuine sum-of-squares Hilbert product. -/
def hodgeEnergySubmodule (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) : Submodule ℝ (HodgeEnergyAmbient g μ) :=
  (Submodule.span ℝ (hodgeEnergyCoreSet g μ hμ)).topologicalClosure

abbrev HodgeEnergySpace (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) := ↥(hodgeEnergySubmodule g μ hμ)

instance hodgeEnergyCompleteSpace (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) : CompleteSpace (HodgeEnergySpace g μ hμ) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

def hodgeEnergyValue (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) : HodgeEnergySpace g μ hμ →L[ℝ] L2FormHilbert g μ 2 :=
  (WithLp.fstL 2 ℝ _ _).comp (hodgeEnergySubmodule g μ hμ).subtypeL

def hodgeEnergyExterior (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) : HodgeEnergySpace g μ hμ →L[ℝ] L2FormHilbert g μ 3 :=
  (WithLp.fstL 2 ℝ _ _).comp
    ((WithLp.sndL 2 ℝ _ _).comp (hodgeEnergySubmodule g μ hμ).subtypeL)

def hodgeEnergyLower (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) : HodgeEnergySpace g μ hμ →L[ℝ] L2FormHilbert g μ 1 :=
  (WithLp.sndL 2 ℝ _ _).comp
    ((WithLp.sndL 2 ℝ _ _).comp (hodgeEnergySubmodule g μ hμ).subtypeL)

def hodgeEnergy (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (u : HodgeEnergySpace g μ hμ) : ℝ :=
  ‖hodgeEnergyExterior g μ hμ u‖ ^ 2 + ‖hodgeEnergyLower g μ hμ u‖ ^ 2

def hodgeEnergyPairing (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (u v : HodgeEnergySpace g μ hμ) : ℝ :=
  inner ℝ (hodgeEnergyExterior g μ hμ u) (hodgeEnergyExterior g μ hμ v) +
    inner ℝ (hodgeEnergyLower g μ hμ u) (hodgeEnergyLower g μ hμ v)

theorem hodgeEnergy_norm_sq (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (u : HodgeEnergySpace g μ hμ) :
    ‖u‖ ^ 2 = ‖hodgeEnergyValue g μ hμ u‖ ^ 2 + hodgeEnergy g μ hμ u := by
  change ‖(u : HodgeEnergyAmbient g μ)‖ ^ 2 = _
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
  rfl

theorem hodgeEnergy_nonnegative (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (u : HodgeEnergySpace g μ hμ) : 0 ≤ hodgeEnergy g μ hμ u :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem hodgeEnergyPairing_self (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (u : HodgeEnergySpace g μ hμ) :
    hodgeEnergyPairing g μ hμ u u = hodgeEnergy g μ hμ u := by
  simp only [hodgeEnergyPairing, real_inner_self_eq_norm_sq, hodgeEnergy]

def hodgeEnergyCore (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M 2)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) : HodgeEnergySpace g μ hμ :=
  ⟨hodgeEnergyCoreTuple g μ hμ A hA hcA, Submodule.le_topologicalClosure _
    (Submodule.subset_span ⟨A, hA, hcA, rfl⟩)⟩

theorem hodgeEnergyCore_energy (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M 2)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) :
    hodgeEnergy g μ hμ (hodgeEnergyCore g μ hμ A hA hcA) =
      (∫ y, formNormSq g.form (exteriorRealForm A) y ∂μ) +
        ∫ y, formNormSq g.form (codifferentialRealForm g.form A) y ∂μ := by
  change ‖realizeActualForm g μ (exteriorRealForm A) _‖ ^ 2 +
    ‖realizeActualForm g μ (codifferentialRealForm g.form A) _‖ ^ 2 = _
  rw [realizeActualForm_norm_sq, realizeActualForm_norm_sq]

end Yau.NodeProofs.P06Aux
