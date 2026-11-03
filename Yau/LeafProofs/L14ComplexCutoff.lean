import Yau.LeafProofs.L14ComplexRows
import Yau.LeafProofs.L03ChartApprox

noncomputable section
open scoped Topology ContDiff
open MeasureTheory Filter Module
open Yau

namespace Yau.LeafProofs.L14Aux

theorem realifiedFirstOrderDerivative_real_mul {X α β ι : Type*}
    (a : β → α → ι → X → ℂ) (η : X → ℝ) :
    realifiedFirstOrderDerivative (fun r c i x => (η x : ℂ) * a r c i x) =
      fun r c i x => η x * realifiedFirstOrderDerivative a r c i x := by
  funext r c i x
  change complexMultiplicationEntryCLM r.2 c.2 ((η x : ℂ) * a r.1 c.1 i x) = _
  simpa only [Complex.real_smul, smul_eq_mul, realifiedFirstOrderDerivative, realifiedFirstOrderValue, realifiedField] using
    (complexMultiplicationEntryCLM r.2 c.2).map_smul (η x) (a r.1 c.1 i x)

theorem realifiedFirstOrderValue_real_mul {X α β : Type*}
    (b : β → α → X → ℂ) (η : X → ℝ) :
    realifiedFirstOrderValue (fun r c x => (η x : ℂ) * b r c x) =
      fun r c x => η x * realifiedFirstOrderValue b r c x := by
  funext r c x
  change complexMultiplicationEntryCLM r.2 c.2 ((η x : ℂ) * b r.1 c.1 x) = _
  simpa only [Complex.real_smul, smul_eq_mul, realifiedFirstOrderDerivative, realifiedFirstOrderValue, realifiedField] using
    (complexMultiplicationEntryCLM r.2 c.2).map_smul (η x) (b r.1 c.1 x)

theorem realifiedField_real_mul {X α : Type*} (u : X → α → ℂ) (η : X → ℝ) :
    realifiedField (fun x c => (η x : ℂ) * u x c) =
      fun x c => η x * realifiedField u x c := by
  funext x c
  change complexCoordinateCLM c.2 ((η x : ℂ) * u x c.1) = _
  simpa only [Complex.real_smul, smul_eq_mul, realifiedFirstOrderDerivative, realifiedFirstOrderValue, realifiedField] using
    (complexCoordinateCLM c.2).map_smul (η x) (u x c.1)

/-- A fixed cutoff restores the original complex system after extending its
coefficients, with an exact commutator involving only the value error. -/
theorem complex_firstOrder_cutoff_graph_tendsto {n : ℕ} {α β ι : Type*}
    [Fintype α] [Fintype ι]
    (ν : Measure (ComplexVector n)) [IsLocallyFiniteMeasure ν]
    (v : ι → ComplexVector n) (a : β → α → ι → ComplexVector n → ℂ)
    (b : β → α → ComplexVector n → ℂ)
    (η : ComplexVector n → ℝ) (hη : ContDiff ℝ ∞ η)
    (hcη : HasCompactSupport η) (hηrange : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1)
    (u : ComplexVector n → α → ℂ) (w : ComplexVector n → β → ℂ)
    (U : ℕ → ComplexVector n → α → ℂ)
    (hU : ∀ j c, ContDiff ℝ ∞ (fun x => U j x c) ∧ HasCompactSupport (fun x => U j x c))
    (hu : ∀ c, MemLp (fun x => u x c) 2 ν) (hw : ∀ r, MemLp (fun x => w x r) 2 ν)
    (htu : ∀ c q, Tendsto (fun j => ∫ x, ‖complexCoordinateCLM q (U j x c - u x c)‖ ^ 2 ∂ν) atTop (𝓝 0))
    (hPm : ∀ j r q, MemLp (fun x => complexCoordinateCLM q (complexFirstOrderSystemApply v
      (fun r c i x => (η x : ℂ) * a r c i x) (fun r c x => (η x : ℂ) * b r c x) (U j) x r)) 2 ν)
    (htP : ∀ r q, Tendsto (fun j => ∫ x, ‖complexCoordinateCLM q (complexFirstOrderSystemApply v
      (fun r c i x => (η x : ℂ) * a r c i x) (fun r c x => (η x : ℂ) * b r c x) (U j) x r - w x r)‖ ^ 2 ∂ν) atTop (𝓝 0))
    (hηu : ∀ x c, (η x : ℂ) * u x c = u x c)
    (hηdu : ∀ x c i, (fderiv ℝ η x (v i) : ℂ) * u x c = 0)
    (hcomm : ∀ r c i, Continuous (fun x => (fderiv ℝ η x (v i) : ℂ) * a r c i x) ∧
      HasCompactSupport (fun x => (fderiv ℝ η x (v i) : ℂ) * a r c i x)) :
    let V := fun j x c => (η x : ℂ) * U j x c
    (∀ j c, ContDiff ℝ ∞ (fun x => V j x c) ∧ HasCompactSupport (fun x => V j x c) ∧
      tsupport (fun x => V j x c) ⊆ tsupport η) ∧
    (∀ c q, Tendsto (fun j => ∫ x, ‖complexCoordinateCLM q (V j x c - u x c)‖ ^ 2 ∂ν) atTop (𝓝 0)) ∧
    ∀ r q, (∀ j, MemLp (fun x => complexCoordinateCLM q
      (complexFirstOrderSystemApply v a b (V j) x r - w x r)) 2 ν) ∧
      Tendsto (fun j => ∫ x, ‖complexCoordinateCLM q
        (complexFirstOrderSystemApply v a b (V j) x r - w x r)‖ ^ 2 ∂ν) atTop (𝓝 0) := by
  classical
  let ar := realifiedFirstOrderDerivative a
  let br := realifiedFirstOrderValue b
  let UR := fun j => realifiedField (U j)
  have hUR (j : ℕ) (c : α × Fin 2) : ContDiff ℝ ∞ (fun x => UR j x c) :=
    (complexCoordinateCLM c.2).contDiff.comp (hU j c.1).1
  have huR (c : α × Fin 2) : MemLp (fun x => realifiedField u x c) 2 ν :=
    (complexCoordinateCLM c.2).comp_memLp' (hu c.1)
  have hwR (r : β × Fin 2) : MemLp (fun x => realifiedField w x r) 2 ν :=
    (complexCoordinateCLM r.2).comp_memLp' (hw r.1)
  have hUm (j : ℕ) (c : α × Fin 2) : MemLp (fun x => UR j x c) 2 ν :=
    (hUR j c).continuous.memLp_of_hasCompactSupport
      ((hU j c.1).2.comp_left (map_zero (complexCoordinateCLM c.2)))
  have hP (j : ℕ) (x : ComplexVector n) (r : β × Fin 2) :
      complexCoordinateCLM r.2 (complexFirstOrderSystemApply v
        (fun r c i x => (η x : ℂ) * a r c i x) (fun r c x => (η x : ℂ) * b r c x) (U j) x r.1) =
      Yau.LeafProofs.L03.firstOrderSystemApply v (fun r c i x => η x * ar r c i x)
        (fun r c x => η x * br r c x) (UR j) x r := by
    simpa only [realifiedFirstOrderDerivative_real_mul, realifiedFirstOrderValue_real_mul] using
      firstOrderSystemApply_realification v (fun r c i x => (η x : ℂ) * a r c i x)
        (fun r c x => (η x : ℂ) * b r c x) (U j) x
        (fun c => (hU j c).1.differentiable (by simp) x) r.1 r.2
  have hcommR (r : β × Fin 2) (c : α × Fin 2) (i : ι) :
      Continuous (fun x => ar r c i x * fderiv ℝ η x (v i)) ∧
        HasCompactSupport (fun x => ar r c i x * fderiv ℝ η x (v i)) := by
    have he : (fun x => ar r c i x * fderiv ℝ η x (v i)) =
        fun x => complexMultiplicationEntryCLM r.2 c.2 ((fderiv ℝ η x (v i) : ℂ) * a r.1 c.1 i x) := by
      funext x
      simpa only [ar, realifiedFirstOrderDerivative, Complex.real_smul, smul_eq_mul, mul_comm] using
        ((complexMultiplicationEntryCLM r.2 c.2).map_smul (fderiv ℝ η x (v i)) (a r.1 c.1 i x)).symm
    rw [he]
    exact ⟨(complexMultiplicationEntryCLM r.2 c.2).continuous.comp (hcomm r.1 c.1 i).1,
      (hcomm r.1 c.1 i).2.comp_left (map_zero _)⟩
  choose C hC using fun r c i => (hcommR r c i).1.bounded_above_of_compact_support (hcommR r c i).2
  have hconv := Yau.LeafProofs.L03.firstOrderSystemApply_cutoff_graph_tendsto ν v ar br η
    (hη.differentiable (by simp)) hη.continuous.aestronglyMeasurable 1 zero_le_one
    (fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hηrange x).1]; exact (hηrange x).2)
    (realifiedField u) (realifiedField w) UR
    (fun j c => (hUR j c).differentiable (by simp)) huR hUm hwR
    (fun c => by simpa only [map_sub, UR, realifiedField] using htu c.1 c.2)
    (fun j r => by simpa only [← hP] using hPm j r.1 r.2)
    (fun r => by simpa only [map_sub, ← hP, realifiedField] using htP r.1 r.2)
    (fun x c => by
      have he := congrArg (complexCoordinateCLM c.2) (hηu x c.1)
      simpa only [← Complex.real_smul, map_smul, smul_eq_mul, realifiedField] using he)
    (fun x c i => by
      have he := congrArg (complexCoordinateCLM c.2) (hηdu x c.1 i)
      simpa only [← Complex.real_smul, map_smul, smul_eq_mul, map_zero, realifiedField] using he)
    (fun r c i => (hcommR r c i).1.aestronglyMeasurable)
    (fun r c i => max 0 (C r c i)) (fun _ _ _ => le_max_left _ _)
    (fun r c i x => (hC r c i x).trans (le_max_right _ _))
  let V := fun j x c => (η x : ℂ) * U j x c
  have hV (j : ℕ) (c : α) : ContDiff ℝ ∞ (fun x => V j x c) :=
    (Complex.ofRealCLM.contDiff.comp hη).mul (hU j c).1
  have hPV (j : ℕ) (x : ComplexVector n) (r : β × Fin 2) :
      complexCoordinateCLM r.2 (complexFirstOrderSystemApply v a b (V j) x r.1) =
        Yau.LeafProofs.L03.firstOrderSystemApply v ar br (fun x c => η x * UR j x c) x r := by
    simpa only [V, realifiedField_real_mul] using firstOrderSystemApply_realification v a b (V j) x
      (fun c => (hV j c).differentiable (by simp) x) r.1 r.2
  refine ⟨?_, ?_, ?_⟩
  · intro j c
    have hs : tsupport (fun x => V j x c) ⊆ tsupport η :=
      tsupport_mul_subset_left.trans (tsupport_comp_subset Complex.ofReal_zero η)
    exact ⟨hV j c, hcη.of_isClosed_subset (isClosed_tsupport _) hs, hs⟩
  · intro c q
    simpa only [V, map_sub, ← Complex.real_smul, map_smul, smul_eq_mul, UR, realifiedField] using hconv.1 (c, q)
  · intro r q
    change (∀ j, MemLp (fun x => complexCoordinateCLM q
      (complexFirstOrderSystemApply v a b (V j) x r - w x r)) 2 ν) ∧
      Tendsto (fun j => ∫ x, ‖complexCoordinateCLM q
        (complexFirstOrderSystemApply v a b (V j) x r - w x r)‖ ^ 2 ∂ν) atTop (𝓝 0)
    have he (j : ℕ) (x : ComplexVector n) :
        complexCoordinateCLM q (complexFirstOrderSystemApply v a b (V j) x r) =
          Yau.LeafProofs.L03.firstOrderSystemApply v ar br (fun x c => η x * UR j x c) x (r, q) :=
      hPV j x (r, q)
    simp_rw [map_sub, he]
    exact hconv.2 (r, q)

end Yau.LeafProofs.L14Aux
