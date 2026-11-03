import Yau.LeafProofs.L14TwoHilbertTest
import Yau.LeafProofs.L14PairFirstOrder

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder ENNReal
open MeasureTheory Bundle Filter Module
namespace Yau.LeafProofs.L14Aux
open BundleDbar

def compactLpField {X : Type*} [MeasurableSpace X] (ν : Measure X) (K : Set X)
    (f : Lp ℂ 2 (ν.restrict K)) : X → ℂ := K.indicator f

theorem compactLpField_memLp {X : Type*} [MeasurableSpace X] (ν : Measure X) (K : Set X)
    (hK : MeasurableSet K) (f : Lp ℂ 2 (ν.restrict K)) : MemLp (compactLpField ν K f) 2 ν :=
  (memLp_indicator_iff_restrict hK.nullMeasurableSet).mpr (Lp.memLp f)

theorem compactLpField_support {X : Type*} [MeasurableSpace X] (ν : Measure X) (K : Set X)
    (f : Lp ℂ 2 (ν.restrict K)) : Function.support (compactLpField ν K f) ⊆ K := by
  intro x hx
  by_contra hn
  exact hx (Set.indicator_of_notMem hn f)

theorem compactLpField_tsupport {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    (ν : Measure X) (K : Set X) (hK : IsClosed K) (f : Lp ℂ 2 (ν.restrict K)) :
    tsupport (compactLpField ν K f) ⊆ K :=
  closure_minimal (compactLpField_support ν K f) hK

theorem compactLpField_ae_restrict {X : Type*} [MeasurableSpace X] (ν : Measure X) (K : Set X)
    (hK : MeasurableSet K) (f : Lp ℂ 2 (ν.restrict K)) :
    compactLpField ν K f =ᵐ[ν.restrict K] f := indicator_ae_eq_restrict hK.nullMeasurableSet

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)] [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]
variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
  (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
  (hKO : K ⊆ localDomain (r := r) E a)

def compactTwoHilbertField (W : WeightedTwoHilbert E g μ hμ h hh φ hφ)
    (z : ComplexVector n) (p : TwoCoefficientIndex n r) : ℂ :=
  compactLpField (lebesgueC n) K (weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hKO p W) z

theorem compactTwoHilbertField_memLp (W : WeightedTwoHilbert E g μ hμ h hh φ hφ)
    (p : TwoCoefficientIndex n r) : MemLp (fun z => compactTwoHilbertField E g μ hμ h hh φ hφ a K hK hKO W z p) 2 (lebesgueC n) :=
  compactLpField_memLp (lebesgueC n) K hK.measurableSet _

theorem compactTwoHilbertField_tsupport (W : WeightedTwoHilbert E g μ hμ h hh φ hφ)
    (p : TwoCoefficientIndex n r) : tsupport (fun z => compactTwoHilbertField E g μ hμ h hh φ hφ a K hK hKO W z p) ⊆ K :=
  compactLpField_tsupport (lebesgueC n) K hK.isClosed _

theorem compactTwoHilbertField_ae_restrict (W : WeightedTwoHilbert E g μ hμ h hh φ hφ)
    (p : TwoCoefficientIndex n r) :
    (fun z => compactTwoHilbertField E g μ hμ h hh φ hφ a K hK hKO W z p) =ᵐ[(lebesgueC n).restrict K]
      weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hKO p W :=
  compactLpField_ae_restrict (lebesgueC n) K hK.measurableSet _

theorem compactTwoHilbertField_skew_ae (W : WeightedTwoHilbert E g μ hμ h hh φ hφ)
    (i j : Fin n) (α : Fin r) :
    (fun z => compactTwoHilbertField E g μ hμ h hh φ hφ a K hK hKO W z ((α,j),i)) =ᵐ[lebesgueC n]
      (fun z => -compactTwoHilbertField E g μ hμ h hh φ hφ a K hK hKO W z ((α,i),j)) := by
  have he := (ae_eq_restrict_iff_indicator_ae_eq hK.measurableSet).mp
    (weightedTwoHilbertLocalCoefficient_skew_ae E g μ hμ h hh φ hφ a K hK hKO i j α W)
  change K.indicator (fun z => weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hKO ((α,j),i) W z) =ᵐ[lebesgueC n] _
  apply he.trans
  exact Eventually.of_forall fun z => by
    change K.indicator (fun z => -weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hKO ((α,i),j) W z) z =
      -K.indicator (fun z => weightedTwoHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hKO ((α,i),j) W z) z
    by_cases hz : z ∈ K
    · rw [Set.indicator_of_mem hz,Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz,Set.indicator_of_notMem hz,neg_zero]

def compactTopHilbertField (U : WeightedTopHilbert E g μ hμ h hh φ hφ)
    (z : ComplexVector n) (α : Fin r) : ℂ :=
  compactLpField (lebesgueC n) K (weightedTopHilbertLocalCoefficient E g μ hμ h hh φ hφ a K hK hKO α U) z

theorem compactTopHilbertField_memLp (U : WeightedTopHilbert E g μ hμ h hh φ hφ)
    (α : Fin r) : MemLp (fun z => compactTopHilbertField E g μ hμ h hh φ hφ a K hK hKO U z α) 2 (lebesgueC n) :=
  compactLpField_memLp (lebesgueC n) K hK.measurableSet _

theorem compactTopHilbertField_tsupport (U : WeightedTopHilbert E g μ hμ h hh φ hφ)
    (α : Fin r) : tsupport (fun z => compactTopHilbertField E g μ hμ h hh φ hφ a K hK hKO U z α) ⊆ K :=
  compactLpField_tsupport (lebesgueC n) K hK.isClosed _

theorem compactTopHilbertField_representative_ae (U : WeightedTopHilbert E g μ hμ h hh φ hφ)
    (α : Fin r) :
    (fun z => compactTopHilbertField E g μ hμ h hh φ hφ a K hK hKO U z α) =ᵐ[(lebesgueC n).restrict K]
      (fun z => coefficients (r := r) E (weightedTopHilbertRepresentative E g μ hμ h hh φ hφ U).1 a z Fin.elim0 α) := by
  have he := weightedTopHilbertLocalCoefficient_realize_ae E g μ hμ h hh φ hφ a K hK hKO α
    (weightedTopHilbertRepresentative E g μ hμ h hh φ hφ U)
  rw [weightedTopHilbertRepresentative_realize] at he
  exact (compactLpField_ae_restrict (lebesgueC n) K hK.measurableSet _).trans he

def compactPairHilbertField (U : WeightedTopHilbert E g μ hμ h hh φ hφ)
    (W : WeightedTwoHilbert E g μ hμ h hh φ hφ) (z : ComplexVector n)
    (c : PairSystemInputIndex n r) : ℂ :=
  match c with
  | .inl α => compactTopHilbertField E g μ hμ h hh φ hφ a K hK hKO U z α
  | .inr p => compactTwoHilbertField E g μ hμ h hh φ hφ a K hK hKO W z p

theorem compactPairHilbertField_memLp (U : WeightedTopHilbert E g μ hμ h hh φ hφ)
    (W : WeightedTwoHilbert E g μ hμ h hh φ hφ) (c : PairSystemInputIndex n r) :
    MemLp (fun z => compactPairHilbertField E g μ hμ h hh φ hφ a K hK hKO U W z c) 2 (lebesgueC n) := by
  cases c with
  | inl α => exact compactTopHilbertField_memLp E g μ hμ h hh φ hφ a K hK hKO U α
  | inr p => exact compactTwoHilbertField_memLp E g μ hμ h hh φ hφ a K hK hKO W p

theorem compactPairHilbertField_tsupport (U : WeightedTopHilbert E g μ hμ h hh φ hφ)
    (W : WeightedTwoHilbert E g μ hμ h hh φ hφ) (c : PairSystemInputIndex n r) :
    tsupport (fun z => compactPairHilbertField E g μ hμ h hh φ hφ a K hK hKO U W z c) ⊆ K := by
  cases c with
  | inl α => exact compactTopHilbertField_tsupport E g μ hμ h hh φ hφ a K hK hKO U α
  | inr p => exact compactTwoHilbertField_tsupport E g μ hμ h hh φ hφ a K hK hKO W p

end Yau.LeafProofs.L14Aux
