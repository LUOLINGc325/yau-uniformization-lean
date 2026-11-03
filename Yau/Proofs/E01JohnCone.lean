import Yau.Proofs.E01ContactSeparation
import Yau.Proofs.E01SphereVariation
import Yau.Proofs.E01DetVariation
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! The actual finite John contact cone, from determinant maximality. -/

noncomputable section
open scoped Matrix ComplexOrder Topology
open Filter Set

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ}

theorem identity_mem_finite_contact_cone
    (v : ComplexVector n → EReal)
    (hv : LowerSemicontinuousOn v (Metric.sphere 0 1))
    (hlower : ∀ η ∈ Metric.sphere (0 : ComplexVector n) 1, (1 : EReal) ≤ v η)
    (hmax : ∀ D : Herm n, D.PosDef →
      (∀ η ∈ Metric.sphere (0 : ComplexVector n) 1,
        (ellipsoidQuadratic D η : EReal) ≤ v η) → D.det.re ≤ 1) :
    (1 : Herm n) ∈ PointedCone.hull ℝ (contactRankOne '' unitContactSet v) := by
  classical
  by_cases hn : n = 0
  · subst n
    have hzero : (1 : Herm 0) = 0 := Subsingleton.elim _ _
    rw [hzero]
    exact (PointedCone.hull ℝ (contactRankOne '' unitContactSet v)).zero_mem
  · by_contra hnot
    obtain ⟨H, hH, htpos, hstrict⟩ := exists_strict_contact_separator
      (Nat.pos_of_ne_zero hn) (unitContactSet v) (isCompact_unitContactSet v hv hlower)
      (fun η hη => unitContactSet_norm hη) hnot
    obtain ⟨δ, hδ, hvar⟩ := exists_small_positive_sphere_variation v hv hlower H hH hstrict
    let f : ℝ → ℝ := fun s => (1 + (s : ℂ) • H).det.re
    have hf : HasDerivAt f (Matrix.trace H).re 0 := determinant_one_line_hasDerivAt H
    have hlocal : IsLocalMaxOn f (Ici 0) 0 := by
      change ∀ᶠ s in 𝓝[Ici (0 : ℝ)] 0, f s ≤ f 0
      filter_upwards [self_mem_nhdsWithin, mem_inf_of_left (Iio_mem_nhds hδ)] with s hs0 hsδ
      by_cases hs : s = 0
      · simp only [hs, le_refl]
      · have hsp : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
        have hV := hvar s hsp hsδ
        simpa [f] using hmax (1 + (s : ℂ) • H) hV.1 hV.2
    have hdir : (1 : ℝ) ∈ posTangentConeAt (Ici (0 : ℝ)) 0 := by
      apply mem_posTangentConeAt_of_segment_subset
      simpa only [zero_add] using
        (convex_Ici (0 : ℝ)).segment_subset (by simp) (by simp)
    have hnonpos : (Matrix.trace H).re ≤ 0 := by
      simpa using hlocal.hasFDerivWithinAt_nonpos hf.hasFDerivAt.hasFDerivWithinAt hdir
    exact (not_le_of_gt htpos) hnonpos

theorem exists_finite_unit_contact_identity
    (v : ComplexVector n → EReal)
    (hv : LowerSemicontinuousOn v (Metric.sphere 0 1))
    (hlower : ∀ η ∈ Metric.sphere (0 : ComplexVector n) 1, (1 : EReal) ≤ v η)
    (hmax : ∀ D : Herm n, D.PosDef →
      (∀ η ∈ Metric.sphere (0 : ComplexVector n) 1,
        (ellipsoidQuadratic D η : EReal) ≤ v η) → D.det.re ≤ 1) :
    ∃ (m : ℕ) (η : Fin m → ComplexVector n) (α : Fin m → ℝ),
      (∀ i, 0 < α i ∧ η i ∈ unitContactSet v) ∧
      (∑ i, (α i : ℂ) • contactRankOne (η i)) = 1 ∧ ∑ i, α i = n := by
  classical
  obtain ⟨m, A, α, hA, hsum⟩ := finite_positive_conic_representation
    (identity_mem_finite_contact_cone v hv hlower hmax)
  have hx : ∀ i, ∃ η, η ∈ unitContactSet v ∧ contactRankOne η = A i :=
    fun i => (hA i).1
  choose η hη heq using hx
  have hsum' : (∑ i, (α i : ℂ) • contactRankOne (η i)) = (1 : Herm n) := by
    simpa only [heq, Complex.coe_smul] using hsum
  refine ⟨m, η, α, (fun i => ⟨(hA i).2, hη i⟩), hsum', ?_⟩
  have htr (i : Fin m) : (Matrix.trace (contactRankOne (η i))).re = 1 := by
    rw [contactRankOne_trace, unitContactSet_norm (hη i)]
    norm_num
  have ht := congrArg (fun M : Herm n => (Matrix.trace M).re) hsum'
  simpa [Matrix.trace_sum, Matrix.trace_smul, Complex.mul_re, htr] using ht

end Yau.NodeProofs.E01Aux
