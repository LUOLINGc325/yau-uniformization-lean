import Yau.Proofs.F01ContinuousRayleigh
import Yau.Proofs.F01LargestRayleighOrder
import Yau.Proofs.F01PositiveMatrixNeighborhood

/-! The largest actual relative eigenvalue is continuous in continuous
positive Hermitian matrix families, without choosing moving eigenvectors. -/
noncomputable section
open Set Filter
open scoped Topology Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
variable {n : ℕ} {A : Type*} [TopologicalSpace A]

theorem largestMatrixRayleigh_eventually_lt
    (G H : A → Matrix (Fin n) (Fin n) ℂ) {a : A}
    (hG : ContinuousAt (fun p => fun i j => G p i j) a)
    (hH : ContinuousAt (fun p => fun i j => H p i j) a)
    (hGp : ∀ p, (G p).PosDef) (hHp : ∀ p, (H p).PosDef)
    {y : ℝ} (hy : largestMatrixRayleigh (G a) (H a) < y) :
    ∀ᶠ p in 𝓝 a, largestMatrixRayleigh (G p) (H p) < y := by
  obtain ⟨c, hc, hcy⟩ := exists_between hy
  let B := fun p => (c : ℂ) • G p - H p
  have hB : ContinuousAt (fun p => fun i j => B p i j) a := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    have hg := (continuous_apply j).continuousAt.comp ((continuous_apply i).continuousAt.comp hG)
    have hh := (continuous_apply j).continuousAt.comp ((continuous_apply i).continuousAt.comp hH)
    exact (continuousAt_const.mul hg).sub hh
  have hherm (p : A) : (B p).IsHermitian :=
    ((hGp p).isHermitian.smul
      (show IsSelfAdjoint (c : ℂ) from Complex.conj_ofReal c)).sub (hHp p).isHermitian
  have hpos : (B a).PosDef := posDef_of_largestMatrixRayleigh_lt (hGp a) (hHp a) hc
  have hcn : 0 ≤ c := (largestMatrixRayleigh_nonneg (hGp a) (hHp a)).trans hc.le
  filter_upwards [eventually_posDef_of_continuousAt_hermitian B hB hherm hpos] with p hp
  exact (largestMatrixRayleigh_le_of_order (hGp p) hcn hp.posSemidef).trans_lt hcy

theorem largestMatrixRayleigh_continuousAt
    (G H : A → Matrix (Fin n) (Fin n) ℂ) {a : A}
    (hG : ContinuousAt (fun p => fun i j => G p i j) a)
    (hH : ContinuousAt (fun p => fun i j => H p i j) a)
    (hGp : ∀ p, (G p).PosDef) (hHp : ∀ p, (H p).PosDef) :
    ContinuousAt (fun p => largestMatrixRayleigh (G p) (H p)) a := by
  apply tendsto_order.mpr
  exact ⟨fun y hy => largestMatrixRayleigh_eventually_gt G H hG hH hGp hHp hy,
    fun y hy => largestMatrixRayleigh_eventually_lt G H hG hH hGp hHp hy⟩

theorem largestMatrixRayleigh_continuousOn
    (G H : A → Matrix (Fin n) (Fin n) ℂ) {s : Set A}
    (hG : ContinuousOn (fun p => fun i j => G p i j) s)
    (hH : ContinuousOn (fun p => fun i j => H p i j) s)
    (hGp : ∀ p ∈ s, (G p).PosDef) (hHp : ∀ p ∈ s, (H p).PosDef) :
    ContinuousOn (fun p => largestMatrixRayleigh (G p) (H p)) s := by
  apply continuousOn_iff_continuous_restrict.mpr
  apply continuous_iff_continuousAt.mpr
  intro p
  exact largestMatrixRayleigh_continuousAt (fun p : s => G p) (fun p : s => H p)
    (continuousOn_iff_continuous_restrict.mp hG).continuousAt
    (continuousOn_iff_continuous_restrict.mp hH).continuousAt
    (fun p => hGp p p.property) (fun p => hHp p p.property)

end Yau.NodeProofs.F01Aux
