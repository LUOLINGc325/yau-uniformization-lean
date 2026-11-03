import Yau.Proofs.F05Reflection
import Yau.LeafProofs.L16HalfSpaceLowInterpolation

/-! Quantitative native reflection for actual one-sided derivative jets.
The raw and lower-jet estimates are reused from the established L16 bounds. -/

open Set
open scoped Topology
noncomputable section
set_option maxHeartbeats 1600000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux

theorem F05_reflection_jet_bounds
    {n : ℕ} {e : Space n} (he : ‖e‖ = 1) {α T K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hK : 0 ≤ K)
    (v : Point n → ℝ) (J₁ : Point n → Space n →L[ℝ] ℝ)
    (J₂ : Point n → Space n →L[ℝ] Space n →L[ℝ] ℝ) (Jt : Point n → ℝ)
    (hv : ContinuousOn v (cylinder {x | 0 ≤ inner ℝ e x} 0 T))
    (hJ₁ : ContinuousOn J₁ (cylinder {x | 0 ≤ inner ℝ e x} 0 T))
    (hJ₂ : ContinuousOn J₂ (cylinder {x | 0 ≤ inner ℝ e x} 0 T))
    (hJt : ContinuousOn Jt (cylinder {x | 0 ≤ inner ℝ e x} 0 T))
    (hD : ∀ p ∈ cylinder {x | 0 < inner ℝ e x} 0 T,
      HasFDerivAt (fun x => v (x,p.2)) (J₁ p) p.1)
    (hDD : ∀ p ∈ cylinder {x | 0 < inner ℝ e x} 0 T,
      HasFDerivAt (fun x => J₁ (x,p.2)) (J₂ p) p.1)
    (ht : ∀ p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T,
      HasDerivWithinAt (fun t => v (p.1,t)) (Jt p) (Icc 0 T) p.2)
    (hBound : ∀ p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T,
      |v p| ≤ K ∧ ‖J₁ p‖ ≤ K ∧ ‖J₂ p‖ ≤ K ∧ |Jt p| ≤ K) :
    let U := halfSpaceSecondOrderExtension e v
    C2 (cylinder univ 0 T) U ∧
      EqOn U v (cylinder {x | 0 ≤ inner ℝ e x} 0 T) ∧
      EqOn (spatialD U) J₁ (cylinder {x | 0 ≤ inner ℝ e x} 0 T) ∧
      EqOn (spatialDD U) J₂ (cylinder {x | 0 ≤ inner ℝ e x} 0 T) ∧
      EqOn (timeD (cylinder univ 0 T) U) Jt (cylinder {x | 0 ≤ inner ℝ e x} 0 T) ∧
      (∀ p ∈ cylinder univ 0 T, |U p| ≤ 500*K ∧ ‖spatialD U p‖ ≤ 500*K ∧
        ‖spatialDD U p‖ ≤ 500*K ∧ |timeD (cylinder univ 0 T) U p| ≤ 500*K) ∧
      HolderBound α (cylinder univ 0 T) (fun p => (U p,spatialD U p)) (8000*K) := by
  let U := halfSpaceSecondOrderExtension e v
  obtain ⟨hU,hV,hG,hH,hTime⟩ :=
    halfSpaceSecondOrderExtension_jets he hT v J₁ J₂ Jt hv hJ₁ hJ₂ hJt hD hDD ht
  have hRaw : ∀ p ∈ cylinder univ 0 T, |U p| ≤ 500*K ∧ ‖spatialD U p‖ ≤ 500*K ∧
      ‖spatialDD U p‖ ≤ 500*K ∧ |timeD (cylinder univ 0 T) U p| ≤ 500*K := by
    have hPhysical : C2 (cylinder {x | 0 ≤ inner ℝ e x} 0 T) U :=
      c2_cylinder_restrict_space hU
    have hPhysicalBound : ∀ p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T,
        |U p| ≤ K ∧ ‖spatialD U p‖ ≤ K ∧ ‖spatialDD U p‖ ≤ K ∧
          |timeD (cylinder {x | 0 ≤ inner ℝ e x} 0 T) U p| ≤ K := by
      intro p hp
      rw [timeD_cylinder_restrict_space U hp]
      dsimp only [U]
      rw [hV hp,hG hp,hH hp,hTime hp]
      exact hBound p hp
    have hR := (halfSpaceSecondOrderExtension_raw_bounds he hT hK hPhysical hPhysicalBound).2.2.2
    simpa only [U,F05_reflection_idempotent he v] using hR
  refine ⟨hU,hV,hG,hH,hTime,hRaw,?_⟩
  have hLow := c2_global_lowPair_holder hα hα1 hT (by positivity : 0 ≤ 500*K) hU
    (fun p hp => ⟨(hRaw p hp).1,(hRaw p hp).2.2.1,(hRaw p hp).2.2.2⟩)
  convert hLow using 1 <;> ring

end Yau.Proofs.F05Aux
