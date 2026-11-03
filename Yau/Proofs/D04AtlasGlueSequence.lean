import Yau.Proofs.D04AtlasGlueCoordinate
import Yau.Proofs.D04Diagonal

open MeasureTheory Filter Set
open scoped Topology Manifold ENNReal

noncomputable section

namespace Yau.Proofs.D04AtlasGlueAux

open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

/-- Every eventual compact upper assertion survives an exact subsequence
factorization of a tail. -/
theorem collapse_of_stage_tail
    {D : Set (ComplexVector n)} {u : ℕ → ComplexVector n → EReal}
    {φ s τ : ℕ → ℕ} {i : ℕ} (hτ : StrictMono τ)
    (hfactor : ∀ k, φ (k + i) = s (τ k)) (hu : PshCollapses D u s) :
    PshCollapses D u φ := by
  intro K hKD hK A
  obtain ⟨N, hN⟩ := hu K hKD hK A
  exact eventually_atTop.mp (D04Aux.eventually_of_subsequence_tail
    (P := fun j => ∀ z ∈ K, u j z ≤ ((-A : ℝ) : EReal)) hτ hfactor
    (eventually_atTop.mpr ⟨N, hN⟩))

/-- The limit, its finite-a.e. class, and its Hartogs assertion are retained
when passing through the strict tail factorization of the diagonal. -/
theorem l1Limit_of_stage_tail
    {D : Set (ComplexVector n)} {u : ℕ → ComplexVector n → EReal}
    {φ s τ : ℕ → ℕ} {i : ℕ} (hτ : StrictMono τ)
    (hfactor : ∀ k, φ (k + i) = s (τ k)) (hu : PshL1Limit D u s) :
    PshL1Limit D u φ := by
  obtain ⟨v, hvpsh, hvnontrivial, hvfinite, hvlocal, hhartogs⟩ := hu
  refine ⟨v, hvpsh, hvnontrivial, hvfinite, ?_, ?_⟩
  · intro K hKD hK
    refine ⟨(hvlocal K hKD hK).1, ?_⟩
    exact D04Aux.tendsto_of_subsequence_tail
      (fun j => ∫⁻ z in K, erealDist (u j z) (v z) ∂lebesgueC n)
      hτ hfactor (hvlocal K hKD hK).2
  · intro c hc K hKD hK ε hε
    obtain ⟨N, hN⟩ := hhartogs c hc K hKD hK ε hε
    exact eventually_atTop.mp (D04Aux.eventually_of_subsequence_tail
      (P := fun j => ∀ z ∈ K, u j z ≤ ((c + ε : ℝ) : EReal)) hτ hfactor
      (eventually_atTop.mpr ⟨N, hN⟩))

/-- Successive coordinate calls are nested before taking the strict
diagonal. Every chart branch concerns the same final original sequence. -/
theorem exists_simultaneous_chart_branches
    (hcoord : PshCompactnessBridge n) (B : ℕ → ChartBall M)
    (Ωs : ℕ → Set M.Carrier) (us : ℕ → M.Carrier → EReal)
    (hΩ : ∀ j, IsOpen (Ωs j) ∧ Ωs j ⊆ Ωs (j + 1))
    (hcover : (⋃ j, Ωs j) = univ)
    (hpsh : ∀ j, PshOnManifold (us j) (Ωs j))
    (hupper : ∀ K : Set M.Carrier, IsCompact K → ∃ C : ℝ, ∀ j,
      K ⊆ Ωs j → ∀ x ∈ K, us j x ≤ (C : EReal)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i,
      PshCollapses (Metric.ball (chartPt (B i).center (B i).center) (2 * (B i).radius))
        (fun j z => us j (chartInv (B i).center z)) φ ∨
      PshL1Limit (Metric.ball (chartPt (B i).center (B i).center) (2 * (B i).radius))
        (fun j z => us j (chartInv (B i).center z)) φ := by
  classical
  let D : ℕ → Set (ComplexVector n) := fun i =>
    Metric.ball (chartPt (B i).center (B i).center) (2 * (B i).radius)
  let Inc := {s : ℕ → ℕ // StrictMono s}
  have hex (i : ℕ) (s : Inc) : ∃ τ : ℕ → ℕ, StrictMono τ ∧
      (PshCollapses (D i) (fun j z => us (s.1 j) (chartInv (B i).center z)) τ ∨
        PshL1Limit (D i) (fun j z => us (s.1 j) (chartInv (B i).center z)) τ) :=
    coordinate_extraction hcoord (B i).center (D i) Metric.isOpen_ball
      (Metric.isConnected_ball (by linarith [(B i).radius_pos]))
      (B i).outer_subset_target Ωs us hΩ hcover hpsh hupper s.1 s.2
  let selected (i : ℕ) (s : Inc) : ℕ → ℕ := Classical.choose (hex i s)
  have hselected (i : ℕ) (s : Inc) : StrictMono (selected i s) :=
    (Classical.choose_spec (hex i s)).1
  let stages : ℕ → Inc := fun m => Nat.rec ⟨id, strictMono_id⟩
    (fun i s => ⟨s.1 ∘ selected i s, s.2.comp (hselected i s)⟩) m
  let r : ℕ → ℕ → ℕ := fun i => selected i (stages i)
  have hrec (i k : ℕ) : (stages (i + 1)).1 k = (stages i).1 (r i k) := rfl
  obtain ⟨φ, hφ, hfactor⟩ := D04Aux.nested_subsequence_diagonal
    (fun i => (stages i).1) r (fun i => (stages i).2)
    (fun i => hselected i (stages i)) hrec
  refine ⟨φ, hφ, ?_⟩
  intro i
  obtain ⟨τ, hτ, hτfactor⟩ := hfactor i
  have hbranch := (Classical.choose_spec (hex i (stages i))).2
  change PshCollapses (D i) _ φ ∨ PshL1Limit (D i) _ φ
  rcases hbranch with hc | hl
  · left
    apply collapse_of_stage_tail hτ hτfactor
    simpa only [PshCollapses, Function.comp_def, hrec, r, selected] using hc
  · right
    apply l1Limit_of_stage_tail hτ hτfactor
    simpa only [PshL1Limit, Function.comp_def, hrec, r, selected] using hl

end Yau.Proofs.D04AtlasGlueAux
