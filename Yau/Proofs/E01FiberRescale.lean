import spec.CHAIN.CONTRACTS
import Yau.Proofs.E01LiminfBounds
import Mathlib.Topology.Algebra.ConstMulAction

/-! The genuine fiber rescaling preserves the exact chart/time domain and its neighborhood filter. -/

noncomputable section
open scoped Topology
open Filter Set

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ}

def fiberRescaleHomeomorph (r : ℝ) (hr : r ≠ 0) :
    (ComplexVector n × ComplexVector n × ℝ) ≃ₜ (ComplexVector n × ComplexVector n × ℝ) :=
  (Homeomorph.refl _).prodCongr
    ((Homeomorph.smulOfNeZero (r : ℂ) (Complex.ofReal_ne_zero.mpr hr)).prodCongr
      (Homeomorph.refl ℝ))

theorem fiberRescaleHomeomorph_apply (r : ℝ) (hr : r ≠ 0)
    (p : ComplexVector n × ComplexVector n × ℝ) :
    fiberRescaleHomeomorph r hr p = (p.1, (r : ℂ) • p.2.1, p.2.2) := rfl

theorem fiberRescaleHomeomorph_image_domain (r : ℝ) (hr : r ≠ 0)
    (S : Set (ComplexVector n)) (I : Set ℝ) :
    fiberRescaleHomeomorph (n := n) r hr '' {p | p.1 ∈ S ∧ p.2.2 ∈ I} =
      {p | p.1 ∈ S ∧ p.2.2 ∈ I} := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp
  · intro hq
    exact ⟨(fiberRescaleHomeomorph r hr).symm q, hq,
      (fiberRescaleHomeomorph r hr).apply_symm_apply q⟩

theorem fiberRescaleHomeomorph_map_nhdsWithin (r : ℝ) (hr : r ≠ 0)
    (S : Set (ComplexVector n)) (I : Set ℝ)
    (p : ComplexVector n × ComplexVector n × ℝ) :
    Filter.map (fiberRescaleHomeomorph r hr) (𝓝[{q | q.1 ∈ S ∧ q.2.2 ∈ I}] p) =
      𝓝[{q | q.1 ∈ S ∧ q.2.2 ∈ I}] (p.1, (r : ℂ) • p.2.1, p.2.2) := by
  rw [(fiberRescaleHomeomorph r hr).isEmbedding.map_nhdsWithin_eq,
    fiberRescaleHomeomorph_image_domain, fiberRescaleHomeomorph_apply]

end Yau.NodeProofs.E01Aux
