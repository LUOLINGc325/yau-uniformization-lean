import Yau.Proofs.G04Whitening
import Yau.Proofs.G04SpectralBounds
import Yau.Proofs.G04TraceSmooth

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.G04Aux
open Yau Yau.Blueprint Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem order_of_norm (h : HermitianField M) (A : RealForm M 2) (hA : RealOneOne A)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, formNormSq h A x ≤ B ^ 2) : FormOrderBound h B A := by
  intro x
  have hH : (gMat h x).PosDef := L12Aux.hMat_posDef h x (chartPt x x) (mem_extChartAt_target x)
  obtain ⟨S, hS, hu, hsq, hSHS⟩ := exists_hermitian_whitening (gMat h x) hH
  have hC := (representsSelf A hA).2 x
  have hQ : (S * formHermitianMatrix A x * S).IsHermitian := by
    simpa only [hS.eq] using Matrix.isHermitian_conjTranspose_mul_mul S hC
  apply (whitening_order_iff (gMat h x) (formHermitianMatrix A x) S hS hu hSHS B).mpr
  apply hermitian_order_of_square_trace _ hQ hB
  rw [whitening_square_trace _ _ _ hsq, ← oneOneNorm h A hA x]
  exact hb x

theorem norm_of_order (h : HermitianField M) (A : RealForm M 2) (hA : RealOneOne A)
    {B : ℝ} (hB : 0 ≤ B) (hb : FormOrderBound h B A) (x : M.Carrier) :
    formNormSq h A x ≤ (n : ℝ) * B ^ 2 := by
  have hH : (gMat h x).PosDef := L12Aux.hMat_posDef h x (chartPt x x) (mem_extChartAt_target x)
  obtain ⟨S, hS, hu, hsq, hSHS⟩ := exists_hermitian_whitening (gMat h x) hH
  have hC := (representsSelf A hA).2 x
  have hQ : (S * formHermitianMatrix A x * S).IsHermitian := by
    simpa only [hS.eq] using Matrix.isHermitian_conjTranspose_mul_mul S hC
  have hbound := (whitening_order_iff (gMat h x) (formHermitianMatrix A x) S hS hu hSHS B).mp (hb x)
  have he := hermitian_square_trace_of_order _ hQ hB hbound
  rw [whitening_square_trace _ _ _ hsq, ← oneOneNorm h A hA x] at he
  exact he

theorem trace_of_order (h : HermitianField M) (A : RealForm M 2) (hA : RealOneOne A)
    {C : ℝ} (hC : 0 ≤ C) (hb : FormOrderBound h C A) (x : M.Carrier) :
    |formTrace h A x| ≤ (n : ℝ) * C := by
  have hH : (gMat h x).PosDef := L12Aux.hMat_posDef h x (chartPt x x) (mem_extChartAt_target x)
  obtain ⟨S, hS, hu, hsq, hSHS⟩ := exists_hermitian_whitening (gMat h x) hH
  have hA' := (representsSelf A hA).2 x
  have hQ : (S * formHermitianMatrix A x * S).IsHermitian := by
    simpa only [hS.eq] using Matrix.isHermitian_conjTranspose_mul_mul S hA'
  have hbound := (whitening_order_iff (gMat h x) (formHermitianMatrix A x) S hS hu hSHS C).mp (hb x)
  have he := hermitian_trace_of_order _ hQ hC hbound
  rw [whitening_trace _ _ _ hsq] at he
  exact he

theorem boundedFormHeatClass_iff_order (h : HermitianField M) (U : ℝ → RealForm M 2)
    (hU : ∀ t, 0 < t → RealOneOne (U t)) :
    BoundedFormHeatClass h U ↔
      ∀ T, 0 < T → ∃ B : ℝ, 0 < B ∧ ∀ t, 0 < t → t ≤ T → FormOrderBound h B (U t) := by
  constructor
  · intro hb T hT
    obtain ⟨B, hB, hbound⟩ := hb T hT
    exact ⟨B, hB, fun t ht htT => order_of_norm h (U t) (hU t ht) hB.le
      (fun x => hbound x t ht htT)⟩
  · intro hb T hT
    obtain ⟨B, hB, hbound⟩ := hb T hT
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    refine ⟨((n : ℝ) + 1) * B, mul_pos (by linarith) hB, ?_⟩
    intro x t ht htT
    calc
      formNormSq h (U t) x ≤ (n : ℝ) * B ^ 2 := norm_of_order h (U t) (hU t ht) hB.le (hbound t ht htT) x
      _ ≤ ((n : ℝ) + 1) ^ 2 * B ^ 2 :=
        mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (n : ℝ)]) (sq_nonneg B)
      _ = _ := by ring

theorem representationBridge (h : HermitianField M) (hs : MetricSmooth h) :
    OneOneRepresentationBridge h :=
  ⟨representsSelf, reconstructSigned,
    ⟨omegaForm h, omegaForm_smooth h hs, omegaForm_oneOne h, omegaForm_represents h⟩,
    boundedFormHeatClass_iff_order h⟩

theorem traceBridge (h : HermitianField M) (hs : MetricSmooth h) : HodgeTraceDataBridge h :=
  ⟨trace_smooth h hs, fun A C hA hC hb => trace_of_order h A hA hC hb⟩

end Yau.NodeProofs.G04Aux
