import Yau.LeafProofs.L05ChuLinearization

noncomputable section

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic Yau.ParabolicCandidates

def chuFrozenLinear {n : ℕ} {T : Sym n → Point n → Sym n} {K beta : ℝ}
    (hT : ChuH2 T K beta) (F : Sym n → Point n → ℝ) (A0 : Sym n) (p0 : Point n)
    (hp0 : p0 ∈ backward 1) : Sym n →ₗ[ℝ] ℝ :=
  (fderiv ℝ (fun N => F N p0) A0).toLinearMap.comp (chuTransformLinear hT p0 hp0)

def chuFrozenSlope {n : ℕ} {T : Sym n → Point n → Sym n} {K beta : ℝ}
    (hT : ChuH2 T K beta) (F : Sym n → Point n → ℝ) (A0 : Sym n) (p0 : Point n)
    (hp0 : p0 ∈ backward 1) : Sym n := dualMatrix (chuFrozenLinear hT F A0 p0 hp0)

theorem chuFrozenLinear_apply {n : ℕ} {T : Sym n → Point n → Sym n} {K beta : ℝ}
    (hT : ChuH2 T K beta) (F : Sym n → Point n → ℝ) (A0 V : Sym n) (p0 : Point n)
    (hp0 : p0 ∈ backward 1) :
    chuFrozenLinear hT F A0 p0 hp0 V=fderiv ℝ (fun N => F N p0) A0 (T V p0) := rfl

theorem chuFrozenLinear_trace {n : ℕ} {T : Sym n → Point n → Sym n} {K beta : ℝ}
    (hT : ChuH2 T K beta) (F : Sym n → Point n → ℝ) (A0 V : Sym n) (p0 : Point n)
    (hp0 : p0 ∈ backward 1) :
    chuFrozenLinear hT F A0 p0 hp0 V=tracePair (chuFrozenSlope hT F A0 p0 hp0) V :=
  dualMatrix_apply _ V

theorem chuFrozenSlope_mem_slopeSet {n : ℕ} {E U : Set (Sym n)}
    {F : Sym n → Point n → ℝ} {T : Sym n → Point n → Sym n} {ell L K beta : ℝ}
    (hell : 0 ≤ ell) (hL : ell ≤ L) (hF : ChuH1 E U F ell L K beta) (hT : ChuH2 T K beta)
    {A0 : Sym n} (hA0 : A0 ∈ E) {p0 : Point n} (hp0 : p0 ∈ backward 1) :
    chuFrozenSlope hT F A0 p0 hp0 ∈ slopeSet n (ell*K⁻¹) (Real.sqrt (Fintype.card (RIdx n))*K*L) := by
  apply dualMatrix_mem_slopeSet
  intro v
  have hTP := (hT.2.2.2 (rankOne v) (rankOne_posSemidef v) p0 hp0).1
  have hA := slopeSet_tracePair_bounds (chuSlope_mem_slopeSet hF hA0 hp0) hTP
  have hTr := chuTransform_trace_bounds hT hp0 (rankOne_posSemidef v)
  rw [rankOne_trace] at hTr
  have hl := mul_le_mul_of_nonneg_left hTr.1 hell
  have hu := mul_le_mul_of_nonneg_left hTr.2 (hell.trans hL)
  rw [chuFrozenLinear_apply,chuSlope_apply]
  constructor <;> nlinarith only [hA.1,hA.2,hl,hu]

theorem chuFrozenLinear_globalElliptic {n : ℕ} {E U : Set (Sym n)}
    {F : Sym n → Point n → ℝ} {T : Sym n → Point n → Sym n} {ell L K beta : ℝ}
    (hell : 0 ≤ ell) (hL : ell ≤ L) (hF : ChuH1 E U F ell L K beta) (hT : ChuH2 T K beta)
    {A0 : Sym n} (hA0 : A0 ∈ E) {p0 : Point n} (hp0 : p0 ∈ backward 1) :
    globalElliptic (chuFrozenLinear hT F A0 p0 hp0) (ell*K⁻¹) (Real.sqrt (Fintype.card (RIdx n))*K*L) := by
  intro N P hP
  rw [map_add,add_sub_cancel_left,chuFrozenLinear_trace]
  exact slopeSet_tracePair_bounds (chuFrozenSlope_mem_slopeSet hell hL hF hT hA0 hp0) hP

end Yau.LeafProofs.L05Aux
