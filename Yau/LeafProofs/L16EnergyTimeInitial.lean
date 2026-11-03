import Yau.LeafProofs.L16LionsTimeTrace

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Yau.LeafProofs.L16EnergyTimeInitial
open Yau.LeafProofs.L16LionsTimeTrace

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def initialTimeTest (T : ℝ) (t : ℝ) : ℝ := 1-t/T

theorem initialTimeTest_smooth (T : ℝ) : ContDiff ℝ ∞ (initialTimeTest T) := by
  exact contDiff_const.sub (contDiff_id.div_const T)

/-- The affine terminal-zero identity inherited from the finite Galerkin
    solutions forces the actual continuous Hilbert trace at zero to vanish. -/
theorem hilbert_initial_trace_zero (j : V →L[ℝ] H) (hj : DenseRange j)
    {T : ℝ} (hT : 0 < T) {U : ℝ → V} {R : ℝ → StrongDual ℝ V} {u : ℝ → H}
    (hR : MemLp R 2 (volume.restrict (Ioo 0 T)))
    (hAE : ∀ᵐ t ∂volume.restrict (Ioo 0 T), j (U t) = u t)
    (hInc : ∀ w : V, ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
      inner ℝ (u t-u s) (j w) = ∫ r in s..t, R r w)
    (hAffine : ∀ w : V,
      (∫ t in Ioo 0 T, deriv (initialTimeTest T) t*inner ℝ (j (U t)) (j w)) =
        -(∫ t in Ioo 0 T, initialTimeTest T t*R t w)) : u 0 = 0 := by
  have hTest0 : initialTimeTest T 0 = 1 := by simp [initialTimeTest]
  have hTestT : initialTimeTest T T = 0 := by simp [initialTimeTest,hT.ne']
  have hPair (w : V) : inner ℝ (u 0) (j w) = 0 := by
    have hIBP := hilbert_trace_pairing_ibp j hT hR hInc w
      ((initialTimeTest_smooth T).of_le (by simp))
    rw [hTest0,hTestT,zero_mul,one_mul,zero_sub] at hIBP
    have hLHS : (∫ t in Ioo 0 T, deriv (initialTimeTest T) t*inner ℝ (u t) (j w)) =
        ∫ t in Ioo 0 T, deriv (initialTimeTest T) t*inner ℝ (j (U t)) (j w) := by
      apply integral_congr_ae
      filter_upwards [hAE] with t ht
      rw [ht]
    rw [hLHS,hAffine w] at hIBP
    linarith
  have hClosed : IsClosed {v : H | inner ℝ (u 0) v = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hRange : Set.range j ⊆ {v : H | inner ℝ (u 0) v = 0} := by
    rintro v ⟨w,rfl⟩
    exact hPair w
  have hAll : (Set.univ : Set H) ⊆ {v : H | inner ℝ (u 0) v = 0} := by
    rw [← hj.closure_range]
    exact closure_minimal hRange hClosed
  have hSelf : inner ℝ (u 0) (u 0) = 0 := hAll (mem_univ _)
  rw [real_inner_self_eq_norm_sq] at hSelf
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hSelf)

end Yau.LeafProofs.L16EnergyTimeInitial
