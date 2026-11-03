import Yau.Proofs.F01LargestRayleigh

/-! Actual fixed-direction quadratic quotients are continuous in matrix
entries. Their supremum has the genuine lower neighborhood bound. -/
noncomputable section
open Set Filter
open scoped Topology Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
variable {n : ℕ} {A : Type*} [TopologicalSpace A]

theorem matrixQuadraticValue_continuousAt
    (G : A → Matrix (Fin n) (Fin n) ℂ) {a : A}
    (hG : ContinuousAt (fun p => fun i j => G p i j) a) (v : Fin n → ℂ) :
    ContinuousAt (fun p => matrixQuadraticValue (G p) v) a := by
  have hij (i j : Fin n) : ContinuousAt (fun p => G p i j) a :=
    (continuous_apply j).continuousAt.comp ((continuous_apply i).continuousAt.comp hG)
  have hh : ContinuousAt (fun p => ∑ i, star (v i) * ∑ j, G p i j * v j) a :=
    tendsto_finsetSum Finset.univ (fun i (_ : i ∈ Finset.univ) => continuousAt_const.mul
      (tendsto_finsetSum Finset.univ (fun j (_ : j ∈ Finset.univ) => (hij i j).mul continuousAt_const)))
  exact Complex.continuous_re.continuousAt.comp hh

theorem matrixRayleigh_continuousAt
    (G H : A → Matrix (Fin n) (Fin n) ℂ) {a : A}
    (hG : ContinuousAt (fun p => fun i j => G p i j) a)
    (hH : ContinuousAt (fun p => fun i j => H p i j) a)
    (hpos : (G a).PosDef) (v : Fin n → ℂ) :
    ContinuousAt (fun p => matrixRayleigh (G p) (H p) v) a := by
  by_cases hv : v = 0
  · subst v
    simpa [matrixRayleigh, matrixQuadraticValue] using
      (continuousAt_const : ContinuousAt (fun _ : A => (0 : ℝ)) a)
  · exact (matrixQuadraticValue_continuousAt H hH v).div
      (matrixQuadraticValue_continuousAt G hG v) (matrixQuadraticValue_pos hpos hv).ne'

theorem largestMatrixRayleigh_eventually_gt
    (G H : A → Matrix (Fin n) (Fin n) ℂ) {a : A}
    (hG : ContinuousAt (fun p => fun i j => G p i j) a)
    (hH : ContinuousAt (fun p => fun i j => H p i j) a)
    (hGp : ∀ p, (G p).PosDef) (hHp : ∀ p, (H p).PosDef)
    {y : ℝ} (hy : y < largestMatrixRayleigh (G a) (H a)) :
    ∀ᶠ p in 𝓝 a, y < largestMatrixRayleigh (G p) (H p) := by
  obtain ⟨b, ⟨v, rfl⟩, hv⟩ := exists_lt_of_lt_csSup (range_nonempty _) hy
  have hq := matrixRayleigh_continuousAt G H hG hH (hGp a) v
  filter_upwards [hq.eventually (Ioi_mem_nhds hv)] with p hp
  exact hp.trans_le (matrixRayleigh_le_largest (hGp p) (hHp p) v)

end Yau.NodeProofs.F01Aux
