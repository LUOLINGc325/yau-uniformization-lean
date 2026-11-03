import Yau.Proofs.V04FejerColumnBounds
import Yau.Proofs.V04FiniteFrequency

/-! The Fourier shift of the original polynomial column has support in
1 through 2P+1. Its original vector seminorm is bounded before any family
limit, using the same circle trace and normalized Fourier coefficients. -/

open MeasureTheory AddCircle
open scoped Topology Matrix ComplexOrder ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem circlePoint_pow_eq_fourier (P : ℕ) (θ : ℝ) :
    circlePoint θ ^ (P + 1) = fourier ((P + 1 : ℕ) : ℤ) (θ : AddCircle (2 * Real.pi)) := by
  rw [fourier_twopi_coe]
  unfold circlePoint
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

variable {n q : ℕ} {X : KahlerManifold n}

theorem fejerTestColumn_boundaryDSq_bound {d : VariationData X q} (hd : VariationSetup d)
    {j a : ℕ} (ha : 4 ≤ a) {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F)
    {E : ℂ → CotangentMatrix n} (hE : NormalizedDiscFrame d.G F.f E) {M : ℝ} (hM : 0 ≤ M)
    (hT : ∀ θ, (boundarySymbol d j a F E (circlePoint θ)).IsHermitian ∧
      rectOpNorm (boundarySymbol d j a F E (circlePoint θ)) ≤ M)
    (P : ℕ) (i : CotangentIndex n) :
    boundaryDSq (fun θ => fejerTestColumn d j a F E P i (circlePoint θ)) ≤
      ENNReal.ofReal ((2 * n : ℕ) * ((2 * P + 1 : ℝ) * M ^ 2)) := by
  let A := fun θ => matrixNegative (boundarySymbol d j a F E (circlePoint θ))
  have hA : ∀ r k, Continuous (fun θ => A θ r k) := matrixNegative_entry_continuous
    (fun r k => (boundarySymbol_trace_contDiff hd j a ha F hF E hE r k).continuous)
    (fun θ => (hT θ).1)
  have hp : ∀ r k, Function.Periodic (fun θ => A θ r k) (2 * Real.pi) :=
    fun r k => circleTrace_periodic (fun z => matrixNegative (boundarySymbol d j a F E z) r k)
  have hentry : ∀ θ r k, ‖A θ r k‖ ≤ M := fun θ r k =>
    (matrix_entry_norm_le_rectOpNorm _ r k).trans
      ((rectOpNorm_negative_le _ (hT θ).1).trans (hT θ).2)
  let l := fun θ => fejerTestColumn d j a F E P i (circlePoint θ)
  have hlp (r : CotangentIndex n) : Function.Periodic (fun θ => l θ r) (2 * Real.pi) :=
    circleTrace_periodic (fun z => fejerTestColumn d j a F E P i z r)
  have hlift (r : CotangentIndex n) : (hlp r).lift =
      fun x => fourier ((P + 1 : ℕ) : ℤ) x * scalarFejer (hp r i).lift P x := by
    funext x
    induction x using Quotient.inductionOn' with
    | h θ =>
      change fejerTestColumn d j a F E P i (circlePoint θ) r = _
      rw [fejerTestColumn_boundary, circlePoint_pow_eq_fourier,
        fejerMean_entry_eq_scalarFejer A hp]
  have hsemi (r : CotangentIndex n) : circleDirichlet (hlp r).lift ≤
      ENNReal.ofReal ((2 * P + 1 : ℝ) * M ^ 2) := by
    rw [hlift]
    apply shifted_scalarFejer_dirichlet_le (periodic_lift_continuous (hp r i) (hA r i)) hM
    intro x
    induction x using Quotient.inductionOn' with
    | h θ => exact hentry θ r i
  change boundaryDSq l ≤ _
  rw [boundaryDSq_eq_sum_periodic_lift l hlp]
  calc
    _ ≤ ∑ _r : CotangentIndex n, ENNReal.ofReal ((2 * P + 1 : ℝ) * M ^ 2) :=
      Finset.sum_le_sum (fun r _ => hsemi r)
    _ = ENNReal.ofReal (∑ _r : CotangentIndex n, ((2 * P + 1 : ℝ) * M ^ 2)) :=
      (ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)).symm
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_add, two_mul]

end Yau.Blueprint.V04Proof
