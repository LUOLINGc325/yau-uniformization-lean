import Yau.LeafProofs.L16EnergyGalerkinSpaces
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual

/-!
# Weak extraction for uniformly bounded Hilbert-space sequences

The compactness input is mathlib's sequential Banach–Alaoglu theorem.  Riesz
representation turns its weak-dual limit into a vector of the original real
Hilbert space.  The results concern actual inner products and continuous linear
functionals, so no separate weak-solution or test-density hypothesis is used.
-/

noncomputable section

open Filter
open scoped Topology

namespace Yau.LeafProofs.L16Aux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A uniform norm bound passes to an inner-product weak limit. -/
theorem norm_le_of_inner_tendsto {u : ℕ → E} {v : E} {M : ℝ}
    (hM : 0 ≤ M) (hu : ∀ n, ‖u n‖ ≤ M)
    (hweak : ∀ w : E, Tendsto (fun n => inner ℝ (u n) w) atTop
      (𝓝 (inner ℝ v w))) : ‖v‖ ≤ M := by
  by_cases hv : v = 0
  · simpa [hv] using hM
  have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hlim : inner ℝ v v ≤ M * ‖v‖ :=
    le_of_tendsto (hweak v) (Filter.Eventually.of_forall fun n =>
      (real_inner_le_norm (u n) v).trans (mul_le_mul_of_nonneg_right (hu n) (norm_nonneg v)))
  apply (mul_le_mul_iff_left₀ hpos).mp
  simpa only [real_inner_self_eq_norm_mul_norm] using hlim

/-- The squared energy bound passes to an inner-product weak limit. -/
theorem norm_sq_le_of_inner_tendsto {u : ℕ → E} {v : E} {C : ℝ}
    (hu : ∀ n, ‖u n‖ ^ 2 ≤ C)
    (hweak : ∀ w : E, Tendsto (fun n => inner ℝ (u n) w) atTop
      (𝓝 (inner ℝ v w))) : ‖v‖ ^ 2 ≤ C := by
  have hC : 0 ≤ C := (sq_nonneg ‖u 0‖).trans (hu 0)
  have hv : ‖v‖ ≤ Real.sqrt C := norm_le_of_inner_tendsto (Real.sqrt_nonneg C)
    (fun n => (Real.le_sqrt (norm_nonneg (u n)) hC).mpr (hu n)) hweak
  exact (Real.le_sqrt (norm_nonneg v) hC).mp hv

variable [CompleteSpace E]

/-- Inner-product weak convergence transports through every actual scalar-valued
bounded linear functional, by the Riesz representation theorem. -/
theorem clm_tendsto_of_inner_tendsto {ι : Type*} {f : Filter ι} {u : ι → E} {v : E}
    (hweak : ∀ w : E, Tendsto (fun i => inner ℝ (u i) w) f
      (𝓝 (inner ℝ v w))) (ℓ : E →L[ℝ] ℝ) :
    Tendsto (fun i => ℓ (u i)) f (𝓝 (ℓ v)) := by
  have h := hweak ((InnerProductSpace.toDual ℝ E).symm ℓ)
  have hriesz (x : E) : inner ℝ x ((InnerProductSpace.toDual ℝ E).symm ℓ) = ℓ x := by
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
  simpa only [hriesz] using h

variable [TopologicalSpace.SeparableSpace E]

/-- A uniformly bounded sequence in a complete separable real Hilbert space has a
strictly increasing inner-product weakly convergent subsequence in the same ball. -/
theorem exists_strictMono_inner_tendsto_of_norm_le (u : ℕ → E) (M : ℝ)
    (hM : 0 ≤ M) (hu : ∀ n, ‖u n‖ ≤ M) :
    ∃ v : E, ‖v‖ ≤ M ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ w : E, Tendsto (fun n => inner ℝ (u (φ n)) w) atTop
        (𝓝 (inner ℝ v w)) := by
  let d : ℕ → WeakDual ℝ E := fun n =>
    StrongDual.toWeakDual ((InnerProductSpace.toDual ℝ E) (u n))
  have hd : ∀ n, d n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ E) M := by
    intro n
    simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
      d, StrongDual.toStrongDual_toWeakDual, LinearIsometryEquiv.norm_map] using hu n
  obtain ⟨a, _ha, φ, hφ, hconv⟩ := WeakDual.isSeqCompact_closedBall (𝕜 := ℝ) E
    (0 : StrongDual ℝ E) M hd
  let v : E := (InnerProductSpace.toDual ℝ E).symm (WeakDual.toStrongDual a)
  have hweak : ∀ w : E, Tendsto (fun n => inner ℝ (u (φ n)) w) atTop
      (𝓝 (inner ℝ v w)) := by
    intro w
    have h := (tendsto_iff_forall_eval_tendsto_topDualPairing.mp hconv) w
    change Tendsto (fun n => inner ℝ (u (φ n)) w) atTop
      (𝓝 ((WeakDual.toStrongDual a) w)) at h
    simpa only [v, InnerProductSpace.toDual_symm_apply] using h
  exact ⟨v, norm_le_of_inner_tendsto hM (fun n => hu (φ n)) hweak, φ, hφ, hweak⟩

/-- The extracted subsequence converges under every bounded scalar linear
functional as well as every fixed inner-product test. -/
theorem exists_strictMono_weak_tendsto_of_norm_le (u : ℕ → E) (M : ℝ)
    (hM : 0 ≤ M) (hu : ∀ n, ‖u n‖ ≤ M) :
    ∃ v : E, ‖v‖ ≤ M ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ w : E, Tendsto (fun n => inner ℝ (u (φ n)) w) atTop
        (𝓝 (inner ℝ v w))) ∧
      (∀ ℓ : E →L[ℝ] ℝ, Tendsto (fun n => ℓ (u (φ n))) atTop (𝓝 (ℓ v))) := by
  obtain ⟨v, hv, φ, hφ, hweak⟩ := exists_strictMono_inner_tendsto_of_norm_le u M hM hu
  exact ⟨v, hv, φ, hφ, hweak, fun ℓ => clm_tendsto_of_inner_tendsto hweak ℓ⟩

/-- The extraction theorem directly accepts the uniform squared bounds used in
Galerkin energy estimates. -/
theorem exists_strictMono_weak_tendsto_of_norm_sq_le (u : ℕ → E) (C : ℝ)
    (hu : ∀ n, ‖u n‖ ^ 2 ≤ C) :
    ∃ v : E, ‖v‖ ^ 2 ≤ C ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ w : E, Tendsto (fun n => inner ℝ (u (φ n)) w) atTop
        (𝓝 (inner ℝ v w))) ∧
      (∀ ℓ : E →L[ℝ] ℝ, Tendsto (fun n => ℓ (u (φ n))) atTop (𝓝 (ℓ v))) := by
  have hC : 0 ≤ C := (sq_nonneg ‖u 0‖).trans (hu 0)
  obtain ⟨v, hv, φ, hφ, hweak, hclm⟩ := exists_strictMono_weak_tendsto_of_norm_le
    u (Real.sqrt C) (Real.sqrt_nonneg C)
    (fun n => (Real.le_sqrt (norm_nonneg (u n)) hC).mpr (hu n))
  exact ⟨v, (Real.le_sqrt (norm_nonneg v) hC).mp hv, φ, hφ, hweak, hclm⟩

open MeasureTheory Yau.Parabolic

/-- The actual Bochner Hilbert space for energy-graph-valued time sections. -/
abbrev EnergyTimeHilbert {n : ℕ} (O : Set (Space n)) (T : ℝ) :=
  Lp (EnergyGraphSpace O) 2 (volume.restrict (Set.Ioo 0 T))

/-- Separability of the actual time Hilbert space follows from the already
constructed spatial graph and the restricted Lebesgue measure. -/
instance energyTimeHilbert_secondCountable {n : ℕ} (O : Set (Space n)) (T : ℝ) :
    SecondCountableTopology (EnergyTimeHilbert O T) := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  exact MeasureTheory.Lp.SecondCountableTopology

/-- Uniform energy bounds give weak extraction in the actual Bochner space,
with convergence under every actual bounded scalar functional. -/
theorem energyTimeHilbert_exists_strictMono_weak_tendsto {n : ℕ}
    (O : Set (Space n)) (T : ℝ) (u : ℕ → EnergyTimeHilbert O T) (C : ℝ)
    (hu : ∀ k, ‖u k‖ ^ 2 ≤ C) :
    ∃ v : EnergyTimeHilbert O T, ‖v‖ ^ 2 ≤ C ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ w : EnergyTimeHilbert O T,
        Tendsto (fun k => inner ℝ (u (φ k)) w) atTop (𝓝 (inner ℝ v w))) ∧
      (∀ ℓ : EnergyTimeHilbert O T →L[ℝ] ℝ,
        Tendsto (fun k => ℓ (u (φ k))) atTop (𝓝 (ℓ v))) :=
  exists_strictMono_weak_tendsto_of_norm_sq_le u C hu

end Yau.LeafProofs.L16Aux
