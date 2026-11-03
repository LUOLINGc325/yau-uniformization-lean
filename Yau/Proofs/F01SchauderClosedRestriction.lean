import Yau.Proofs.F01AffineParabolicC2
import Yau.Proofs.F01InteriorSchauderTransfer
import Yau.Proofs.F01AffineParabolicHolder

/-! Genuine closed-cylinder Schauder estimates restrict to smaller
closed cylinders. The temporal derivative is identified using its
within derivative, including both new time faces. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem schauderBound_closed_cylinder_restrict
    {S S' : Set (Space n)} {a b l r β C : ℝ} {u : Point n → ℝ}
    (hlr : l < r) (hS : S' ⊆ S) (hI : Icc l r ⊆ Icc a b)
    (hu : SchauderBound β (cylinder S a b) u C) :
    SchauderBound β (cylinder S' l r) u C := by
  have hSpace : MapsTo (fun x : Space n => (1 : ℝ) • x + 0) S' S := by
    intro x hx
    simpa only [one_smul, add_zero] using hS hx
  have hTime : MapsTo (fun t : ℝ => 0 + (1 : ℝ) ^ 2 * t) (Icc l r) (Icc a b) := by
    intro t ht
    simpa only [one_pow, one_mul, zero_add] using hI ht
  have hPull : affineParabolicPullback 1 (0 : Space n) 0 u = u := by
    funext p
    simp [affineParabolicPullback, affineParabolicPoint]
  have hPoint (p : Point n) : affineParabolicPoint 1 (0 : Space n) 0 p = p := by
    simp [affineParabolicPoint]
  have hSub : cylinder S' l r ⊆ cylinder S a b := fun p hp => ⟨hS hp.1, hI hp.2⟩
  have hC2 : C2 (cylinder S' l r) u := by
    have hh := c2_affineParabolicPullback hlr hu.1 hSpace hTime
    rw [hPull] at hh
    exact hh
  have hEq (p : Point n) (hp : p ∈ cylinder S' l r) :
      timeD (cylinder S' l r) u p = timeD (cylinder S a b) u p := by
    have hh := timeD_affineParabolicPullback hlr hu.1 hSpace hTime hp
    rw [hPull, hPoint] at hh
    simpa only [one_pow, one_mul] using hh
  refine ⟨hC2, hu.2.1, fun p hp => hu.2.2.1 p (hSub hp),
    holderBound_restrict hu.2.2.2.1 hSub, ?_⟩
  apply holderBound_congr_on_native (holderBound_restrict hu.2.2.2.2 hSub)
  intro p hp
  exact (hEq p hp).symm

theorem schauderBound_mono_const {Q : Set (Point n)} {β C D : ℝ}
    {u : Point n → ℝ} (hu : SchauderBound β Q u C) (hCD : C ≤ D) :
    SchauderBound β Q u D := by
  exact ⟨hu.1, hu.2.1.trans hCD,
    fun p hp => ⟨((hu.2.2.1 p hp).1).trans hCD, ((hu.2.2.1 p hp).2).trans hCD⟩,
    holderBound_mono_const hu.2.2.2.1 hCD, holderBound_mono_const hu.2.2.2.2 hCD⟩

end Yau.NodeProofs.F01Aux
