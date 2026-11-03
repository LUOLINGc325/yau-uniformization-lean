import Yau.Proofs.F04CompactCoefficientTest
import Yau.LeafProofs.L19HeatRegularityWeakGradient

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace
noncomputable section
namespace Yau.F04Proof
open Yau.LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}

/-- The genuine flux-plus-drift test for one nondivergence matrix entry. -/
def chartWeakTestEntry (a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
    (η : ComplexVector n → ℝ) (i j : RIdx n) (z : ComplexVector n) : ℝ :=
  a z i j * rDeriv η z i + rDeriv (fun w => a w i j) z i * η z

theorem chartWeakTestEntry_memLp
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    {a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ}
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun z => a z i j) O)
    {η : ComplexVector n → ℝ} (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η)
    (hηO : tsupport η ⊆ O) (i j : RIdx n) :
    MemLp (chartWeakTestEntry a η i j) 2 volume :=
  compactCoefficient_direction_memLp volume hO hη hcη hηO (ha i j) (realVec i)

def chartWeakTestEntryLp
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    {a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ}
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun z => a z i j) O)
    {η : ComplexVector n → ℝ} (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η)
    (hηO : tsupport η ⊆ O) (i j : RIdx n) : Lp ℝ 2 (volume.restrict O) :=
  ((chartWeakTestEntry_memLp hO ha hη hcη hηO i j).mono_measure Measure.restrict_le_self).toLp _

theorem chartWeakTestEntryLp_coe
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    {a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ}
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun z => a z i j) O)
    {η : ComplexVector n → ℝ} (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η)
    (hηO : tsupport η ⊆ O) (i j : RIdx n) :
    chartWeakTestEntryLp hO ha hη hcη hηO i j =ᵐ[volume.restrict O]
      chartWeakTestEntry a η i j :=
  ((chartWeakTestEntry_memLp hO ha hη hcη hηO i j).mono_measure Measure.restrict_le_self).coeFn_toLp

/-- The exact local flux-plus-drift integral is a finite sum of genuine L2
 pairings with the already constructed bounded chart differential maps. -/
theorem scalarEnergy_chartWeakTest_integral
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (c : M.Carrier) {O : Set (ComplexVector n)} (hO : IsOpen O)
    (hOC : IsCompact (closure O)) (hOt : closure O ⊆ chartTarget c)
    {a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ}
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun z => a z i j) O)
    (v : ScalarEnergySpace g μ hμ)
    {η : ComplexVector n → ℝ} (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η)
    (hηO : tsupport η ⊆ O) :
    (∑ i, ∑ j, inner ℝ (scalarEnergy_chartDerivativeCLM g μ hμ c hO hOC hOt j v)
      (chartWeakTestEntryLp hO ha hη hcη hηO i j)) =
      ∫ z in O, ∑ i, ∑ j, scalarEnergy_chartDerivativeCLM g μ hμ c hO hOC hOt j v z *
        chartWeakTestEntry a η i j z := by
  let D := fun j => scalarEnergy_chartDerivativeCLM g μ hμ c hO hOC hOt j v
  have hi (i j : RIdx n) : Integrable (fun z => D j z * chartWeakTestEntry a η i j z)
      (volume.restrict O) :=
    (Lp.memLp (D j)).integrable_mul
      ((chartWeakTestEntry_memLp hO ha hη hcη hηO i j).mono_measure Measure.restrict_le_self)
  have hp (i j : RIdx n) : inner ℝ (D j) (chartWeakTestEntryLp hO ha hη hcη hηO i j) =
      ∫ z in O, D j z * chartWeakTestEntry a η i j z := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [chartWeakTestEntryLp_coe hO ha hη hcη hηO i j] with z hz
    rw [hz]
    simp only [RCLike.inner_apply, conj_trivial, mul_comm]
  change (∑ i, ∑ j, inner ℝ (D j) _) = _
  simp_rw [hp]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  exact (integral_finsetSum Finset.univ (fun j _ => hi i j)).symm

end Yau.F04Proof
