import Yau.Proofs.E01QuadraticFiber
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Compactness.Compact

/-! Uniform persistence of a strictly shrunken feasible matrix. -/

noncomputable section
open scoped Matrix ComplexOrder Topology
open Filter Set

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

theorem isOpen_strict_lsc_real_comparison
    {E : Type*} [TopologicalSpace E] (f : E → ℝ) (hf : Continuous f)
    (v : E → EReal) (hv : LowerSemicontinuous v) :
    IsOpen {x : E | (f x : EReal) < v x} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨b, hfb, hbv⟩ := EReal.exists_between_coe_real hx
  have hfb' : f x < b := EReal.coe_lt_coe_iff.mp hfb
  filter_upwards [(isOpen_lt hf continuous_const).mem_nhds hfb', hv x (b : EReal) hbv]
    with y hyf hyv
  exact (EReal.coe_lt_coe_iff.mpr hyf).trans hyv

theorem open_compact_fiber_persists
    {P E : Type*} [TopologicalSpace P] [TopologicalSpace E]
    (K : Set E) (hK : IsCompact K) (O : Set (P × E)) (hO : IsOpen O)
    (p₀ : P) (hsub : ∀ η ∈ K, (p₀, η) ∈ O) :
    ∃ U : Set P, IsOpen U ∧ p₀ ∈ U ∧ ∀ p ∈ U, ∀ η ∈ K, (p, η) ∈ O := by
  have hprod : ({p₀} : Set P) ×ˢ K ⊆ O := by
    rintro ⟨p, η⟩ ⟨hp, hη⟩
    have hp₀ : p = p₀ := Set.mem_singleton_iff.mp hp
    subst p
    exact hsub η hη
  obtain ⟨U, V, hU, _hV, hpU, hsV, hUV⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := p₀)) hK hO hprod
  exact ⟨U, hU, hpU (Set.mem_singleton p₀), fun p hp η hη => hUV ⟨hp, hsV hη⟩⟩

theorem shrunken_quadratic_strict
    {n : ℕ} (D : Herm n) (hD : D.PosDef) (r : ℝ) (hr : r < 1)
    (η : ComplexVector n) (hη : η ≠ 0) :
    ellipsoidQuadratic ((r : ℂ) • D) η < ellipsoidQuadratic D η := by
  rw [ellipsoidQuadratic_real_smul]
  have hqpos : 0 < ellipsoidQuadratic D η := ellipsoidQuadratic_pos hD hη
  simpa only [one_mul] using mul_lt_mul_of_pos_right hr hqpos

theorem strict_shrink_persists_on_sphere
    {n : ℕ} {P : Type*} [TopologicalSpace P]
    (v : P × ComplexVector n → EReal) (hv : LowerSemicontinuous v)
    (p₀ : P) (D : Herm n) (hD : D.PosDef)
    (hfeasible : ∀ η, (ellipsoidQuadratic D η : EReal) ≤ v (p₀, η))
    (r : ℝ) (hr : r < 1) :
    ∃ U : Set P, IsOpen U ∧ p₀ ∈ U ∧ ∀ p ∈ U,
      ∀ η ∈ Metric.sphere (0 : ComplexVector n) 1,
        (ellipsoidQuadratic ((r : ℂ) • D) η : EReal) < v (p, η) := by
  let O : Set (P × ComplexVector n) :=
    {p | (ellipsoidQuadratic ((r : ℂ) • D) p.2 : EReal) < v p}
  have hO : IsOpen O := isOpen_strict_lsc_real_comparison _
    ((continuous_ellipsoidQuadratic_fiber _).comp continuous_snd) v hv
  have hsub : ∀ η ∈ Metric.sphere (0 : ComplexVector n) 1, (p₀, η) ∈ O := by
    intro η hη
    have hη0 : η ≠ 0 := by
      intro hz
      simp [hz] at hη
    exact (EReal.coe_lt_coe_iff.mpr (shrunken_quadratic_strict D hD r hr η hη0)).trans_le
      (hfeasible η)
  exact open_compact_fiber_persists _ (isCompact_sphere (0 : ComplexVector n) 1) O hO p₀ hsub

end Yau.NodeProofs.E01Aux
