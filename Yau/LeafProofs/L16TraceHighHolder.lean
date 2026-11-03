import Yau.LeafProofs.L16TraceLowContinuity
import Yau.LeafProofs.L16TraceHessianField

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates
local instance traceHighHolder_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance traceHighHolder_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance traceHighHolder_bilinearGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance traceHighHolder_bilinearSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

/-- Real three-parameter kernel bounds transport to the physical half space.
The two spatial parameters are a nonexpansive projection and a unit normal. -/
theorem traceParameterField_holder {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {α T F Cs Ch : ℝ} (hα : 0 ≤ α) (hT1 : T ≤ 1) (hF : 0 ≤ F)
    (hCs : 0 ≤ Cs) (hCh : 0 ≤ Ch) {e : Space n} (he : ‖e‖ = 1)
    (J : ℝ → ℝ → Space n → E)
    (hSup : ∀ t ∈ Icc 0 1, ∀ a, 0 ≤ a → ∀ ξ, ‖J t a ξ‖ ≤ Cs*F)
    (hPair : ∀ ξ η a b t s, 0 ≤ a → 0 ≤ b → t ∈ Icc 0 1 → s ∈ Icc 0 1 →
      ‖J t a ξ-J s b η‖ ≤ Ch*F*(‖ξ-η‖^α+|a-b|^α+|t-s|^(α/2))) :
    HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T)
      (fun p => J p.2 (inner ℝ e p.1) (halfSpaceBoundaryProjection e p.1)) ((Cs+2*Ch)*F) := by
  have hC : 0 ≤ Cs+2*Ch := by positivity
  refine ⟨mul_nonneg hC hF,?_,?_⟩
  · intro p hp
    exact (hSup p.2 ⟨hp.2.1,hp.2.2.trans hT1⟩ _ hp.1 _).trans
      (mul_le_mul_of_nonneg_right (by linarith : Cs ≤ Cs+2*Ch) hF)
  · intro p hp q hq
    have h := hPair (halfSpaceBoundaryProjection e p.1) (halfSpaceBoundaryProjection e q.1)
      (inner ℝ e p.1) (inner ℝ e q.1) p.2 q.2 hp.1 hq.1
      ⟨hp.2.1,hp.2.2.trans hT1⟩ ⟨hq.2.1,hq.2.2.trans hT1⟩
    have hProjection := Real.rpow_le_rpow (norm_nonneg _)
      (halfSpaceBoundaryProjection_nonexpansive e p.1 q.1) hα
    have hNormal : |inner ℝ e p.1-inner ℝ e q.1|^α ≤ ‖p.1-q.1‖^α := by
      apply Real.rpow_le_rpow (abs_nonneg _) _ hα
      simpa only [inner_sub_right,he,one_mul] using abs_real_inner_le_norm e (p.1-q.1)
    have hWeight : ‖halfSpaceBoundaryProjection e p.1-halfSpaceBoundaryProjection e q.1‖^α+
        |inner ℝ e p.1-inner ℝ e q.1|^α+|p.2-q.2|^(α/2) ≤ 2*holderWeight α p q := by
      dsimp only [holderWeight]
      linarith [Real.rpow_nonneg (abs_nonneg (p.2-q.2)) (α/2)]
    exact h.trans ((mul_le_mul_of_nonneg_left hWeight (mul_nonneg hCh hF)).trans
      (by have hw : 0 ≤ holderWeight α p q := by dsimp [holderWeight]; positivity
          nlinarith [mul_nonneg (mul_nonneg hCs hF) hw]))

/-- The actual tangent Hessian, sampled in physical half-space coordinates,
    has a uniform full parabolic Holder bound on every slab of length at most one. -/
theorem normalTraceTangentialSecond_physical_holder {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (e : Space n), ‖e‖ = 1 → ∀ T, T ≤ 1 →
      ∀ (B : Point n → ℝ) F, HolderBound α univ B F →
      HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T)
        (fun p => normalTraceTangentialSecond B p.2 (inner ℝ e p.1)
          (halfSpaceBoundaryProjection e p.1)) (C*F) := by
  obtain ⟨Cs,hCs,hSup⟩ := normalTraceTangentialSecond_bound (n := n) hα
  obtain ⟨Ch,hCh,hPair⟩ := normalTraceTangentialSecond_holder_bound (n := n) hα hα1
  refine ⟨Cs+2*Ch,by positivity,?_⟩
  intro e he T hT1 B F hB
  have hF0 : 0 ≤ F := hB.1
  have hc : Continuous B := continuousOn_univ.mp (holderBound_continuousOn hα hB)
  have hb : ∀ p, |B p| ≤ F := fun p => hB.2.1 p (mem_univ _)
  have hh : ∀ s x y, |B (x,s)-B (y,s)| ≤ F*‖x-y‖^α := by
    intro s x y
    simpa only [holderWeight,sub_self,abs_zero,Real.zero_rpow (by positivity : α/2 ≠ 0),
      add_zero,Real.norm_eq_abs] using hB.2.2 (x,s) (mem_univ _) (y,s) (mem_univ _)
  apply traceParameterField_holder hα.le hT1 hB.1 hCs.le hCh.le he
    (normalTraceTangentialSecond B) ?_ (hPair B F hB)
  intro t ht a ha ξ
  have hPow : t^(α/2) ≤ 1 := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow ht.1 ht.2 (by positivity : 0 ≤ α/2)
  exact (hSup B F F hc hb hB.1 hh t ht.1 a ha ξ).trans
    (mul_le_of_le_one_right (by positivity) hPow)

/-- The actual mixed normal/tangent jet has the same physical Holder estimate;
its nonzero lateral boundary value is retained. -/
theorem normalTraceMixed_physical_holder {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (e : Space n), ‖e‖ = 1 → ∀ T, T ≤ 1 →
      ∀ (B : Point n → ℝ) F, HolderBound α univ B F →
      HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T)
        (fun p => normalTraceMixed B p.2 (inner ℝ e p.1)
          (halfSpaceBoundaryProjection e p.1)) (C*F) := by
  obtain ⟨Cs,hCs,hSup⟩ := normalTraceMixed_bound (n := n) hα
  obtain ⟨Ch,hCh,hPair⟩ := normalTraceMixed_holder_bound (n := n) hα hα1
  refine ⟨Cs+2*Ch,by positivity,?_⟩
  intro e he T hT1 B F hB
  have hF0 : 0 ≤ F := hB.1
  have hc : Continuous B := continuousOn_univ.mp (holderBound_continuousOn hα hB)
  have hb : ∀ p, |B p| ≤ F := fun p => hB.2.1 p (mem_univ _)
  have hh : ∀ s x y, |B (x,s)-B (y,s)| ≤ F*‖x-y‖^α := by
    intro s x y
    simpa only [holderWeight,sub_self,abs_zero,Real.zero_rpow (by positivity : α/2 ≠ 0),
      add_zero,Real.norm_eq_abs] using hB.2.2 (x,s) (mem_univ _) (y,s) (mem_univ _)
  apply traceParameterField_holder hα.le hT1 hB.1 hCs.le hCh.le he
    (normalTraceMixed B) ?_ (hPair B F hB)
  intro t ht a ha ξ
  have hPow : t^(α/2) ≤ 1 := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow ht.1 ht.2 (by positivity : 0 ≤ α/2)
  exact (hSup B F F hc hb hB.1 hh t ht.1 a ξ).trans
    (mul_le_of_le_one_right (by positivity) hPow)

/-- A fixed linear contraction preserves the complete Holder budget. -/
theorem holderBound_comp_linear_contraction {n : ℕ} {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {α C : ℝ} {Q : Set (Point n)} {f : Point n → E} (L : E →L[ℝ] G)
    (hL : ∀ v, ‖L v‖ ≤ ‖v‖) (hf : HolderBound α Q f C) :
    HolderBound α Q (fun p => L (f p)) C := by
  refine ⟨hf.1,fun p hp => (hL _).trans (hf.2.1 p hp),?_⟩
  intro p hp q hq
  rw [← map_sub]
  exact (hL _).trans (hf.2.2 p hp q hq)

/-- The complete physical Hessian has a full parabolic Holder bound on the
    closed half space, with both mixed blocks and the actual Poisson trace. -/
theorem boundaryTraceHessian_holder {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (e : Space n), ‖e‖ = 1 → ∀ T, T ≤ 1 →
      ∀ (B : Point n → ℝ) F, HolderBound α univ B F →
      HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) (boundaryTraceHessian e B) (C*F) := by
  obtain ⟨CT,hCT,hTT⟩ := normalTraceTangentialSecond_physical_holder (n := n) hα hα1
  obtain ⟨CM,hCM,hMM⟩ := normalTraceMixed_physical_holder (n := n) hα hα1
  obtain ⟨CP,hCP,hPP⟩ := tracePoissonAverage_halfSpace_holder (n := n) hα hα1
  refine ⟨CT+2*CM+CP,by positivity,?_⟩
  intro e he T hT1 B F hB
  let P := halfSpaceBoundaryProjection e
  let Q := cylinder {x | 0 ≤ inner ℝ e x} 0 T
  let TT := fun p : Point n => normalTraceTangentialSecond B p.2 (inner ℝ e p.1) (P p.1)
  let MM := fun p : Point n => normalTraceMixed B p.2 (inner ℝ e p.1) (P p.1)
  let PP := fun p : Point n => tracePoissonAverage (inner ℝ e p.1) B (P p.1,p.2)
  let LT := traceHessianPullback P
  let LM := (traceNormalTensorMap e).comp (traceGradientPullback P)
  let LF := (ContinuousLinearMap.flipₗᵢ ℝ (Space n) (Space n) ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  let R := (innerSL ℝ e).smulRight (innerSL ℝ e)
  let LN := (ContinuousLinearMap.id ℝ ℝ).smulRight R
  have hP : ‖P‖ ≤ 1 := halfSpaceBoundaryProjection_norm_le e
  have hT : HolderBound α Q (fun p => LT (TT p)) (CT*F) :=
    holderBound_comp_linear_contraction LT (traceHessianPullback_bound hP) (hTT e he T hT1 B F hB)
  have hM : HolderBound α Q (fun p => LM (MM p)) (CM*F) :=
    holderBound_comp_linear_contraction LM (fun v => by
      change ‖traceNormalTensorMap e (traceGradientPullback P v)‖ ≤ ‖v‖
      rw [traceNormalTensorMap_bound he]
      exact traceGradientPullback_bound hP v) (hMM e he T hT1 B F hB)
  have hMF : HolderBound α Q (fun p => LF (LM (MM p))) (CM*F) :=
    holderBound_comp_linear_contraction LF (fun v => (ContinuousLinearMap.opNorm_flip v).le) hM
  have hR : ‖R‖ = 1 := by
    rw [ContinuousLinearMap.norm_smulRight_apply,innerSL_apply_norm,he,one_mul]
  have hN : HolderBound α Q (fun p => LN (PP p)) (CP*F) :=
    holderBound_comp_linear_contraction LN (fun v => by
      change ‖v • R‖ ≤ ‖v‖
      rw [norm_smul,hR,mul_one])
      (holderBound_mono (hPP e he B F hB) (fun p hp => hp.1))
  have h := holderBound_sub (holderBound_add (holderBound_add hT hM) hMF) hN
  convert h using 1 <;> try rfl
  ring

/-- The actual time derivative field in physical coordinates. -/
def boundaryTraceTimeJet {n : ℕ} (e : Space n) (B : Point n → ℝ) (p : Point n) : ℝ :=
  normalTraceTimeJet B (inner ℝ e p.1) (halfSpaceBoundaryProjection e p.1,p.2)

/-- The physical time jet obeys the complete closed-half-space Holder bound. -/
theorem boundaryTraceTimeJet_holder {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (e : Space n), ‖e‖ = 1 → ∀ T, T ≤ 1 →
      ∀ (B : Point n → ℝ) F, HolderBound α univ B F →
      HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) (boundaryTraceTimeJet e B) (C*F) := by
  obtain ⟨CT,hCT,hTT⟩ := normalTraceTangentialSecond_physical_holder (n := n) hα hα1
  obtain ⟨CP,hCP,hPP⟩ := tracePoissonAverage_halfSpace_holder (n := n) hα hα1
  refine ⟨1+‖heatTrace (n := n)‖*CT+CP,by positivity,?_⟩
  intro e he T hT1 B F hB
  let P := halfSpaceBoundaryProjection e
  let Q := cylinder {x | 0 ≤ inner ℝ e x} 0 T
  have hSource : HolderBound α Q (fun p => B (P p.1,p.2)) F := by
    refine ⟨hB.1,fun p hp => hB.2.1 _ (mem_univ _),?_⟩
    intro p hp q hq
    apply (hB.2.2 (P p.1,p.2) (mem_univ _) (P q.1,q.2) (mem_univ _)).trans
    apply mul_le_mul_of_nonneg_left _ hB.1
    dsimp only [holderWeight]
    exact add_le_add (Real.rpow_le_rpow (norm_nonneg _)
      (halfSpaceBoundaryProjection_nonexpansive e p.1 q.1) hα.le) le_rfl
  have hT := holderBound_comp_continuousLinearMap (heatTrace (n := n)) (hTT e he T hT1 B F hB)
  have hP : HolderBound α Q (fun p => tracePoissonAverage (inner ℝ e p.1) B (P p.1,p.2)) (CP*F) :=
    holderBound_mono (hPP e he B F hB) (fun p hp => hp.1)
  have h := holderBound_sub (holderBound_add hSource hT) hP
  convert h using 1 <;> try rfl
  ring

end Yau.LeafProofs.L16Aux
