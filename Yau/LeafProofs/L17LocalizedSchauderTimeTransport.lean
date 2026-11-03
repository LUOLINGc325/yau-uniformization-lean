import Yau.LeafProofs.L17LocalizedSchauderTransport
import Mathlib.Topology.Order.ProjIcc

open Set Metric Filter
open scoped Topology Classical
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalizedSchauderAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem localizedTerm_tsupport_subset (P : UniformChartPartition g) (T : ℝ) (p : P.centers)
    (v : ComplexVector n × Time T → ℝ) (t : Time T) :
    tsupport (fun x => localizedTerm P T p v (x,t)) ⊆ P.charts.chart p '' closedBall 0 P.radius := by
  apply closure_minimal _ (cutoff_cover_isCompact P p).isClosed
  intro x hx
  by_contra hn
  exact hx (localizedTerm_zero_of_not_cover P T p v (x,t) hn)

theorem localizedTerm_zero_neighborhood (P : UniformChartPartition g) (T : ℝ) (p : P.centers)
    (v : ComplexVector n × Time T → ℝ) {x : M.Carrier}
    (hx : x ∉ P.charts.chart p '' closedBall 0 P.radius) :
    ∀ᶠ y in 𝓝 x, ∀ t : Time T, localizedTerm P T p v (y,t) = 0 := by
  filter_upwards [((cutoff_cover_isCompact P p).isClosed.isOpen_compl.mem_nhds hx)] with y hy t
  exact localizedTerm_zero_of_not_cover P T p v (y,t) hy

theorem localizedTerm_abs_le (P : UniformChartPartition g) (T : ℝ) (p : P.centers)
    (v : ComplexVector n × Time T → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hv : ∀ z ∈ ball (0 : ComplexVector n) (2*P.radius), ∀ t, |v (z,t)| ≤ C) (q : Cylinder M T) :
    |localizedTerm P T p v q| ≤ C := by
  by_cases hx : q.1 ∈ P.charts.chart p '' closedBall 0 P.radius
  · have hz := (inverseChart_mem_of_cover P p hx).2
    have hz' : (P.charts.chart p).symm q.1 ∈ ball (0 : ComplexVector n) (2*P.radius) :=
      mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz) (by have := P.radius_pos; linarith))
    have hχ : P.localization p q.1 ∈ Icc (0 : ℝ) 1 :=
      chartLocalization_mem_Icc (P.charts.chart p) P.radius_pos q.1
    rw [localizedTerm,abs_mul,abs_of_nonneg hχ.1]
    calc
      _ ≤ 1*|v ((P.charts.chart p).symm q.1,q.2)| :=
        mul_le_mul_of_nonneg_right hχ.2 (abs_nonneg _)
      _ ≤ C := by simpa only [one_mul] using hv _ hz' q.2
  · rw [localizedTerm_zero_of_not_cover P T p v q hx,abs_zero]
    exact hC

theorem localizedTerm_hasDerivWithinAt (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    (p : P.centers) (v b : ComplexVector n × Time T → ℝ)
    (hv : ∀ z ∈ ball (0 : ComplexVector n) (2*P.radius), ∀ t : Time T,
      HasDerivWithinAt (fun τ => v (z,projIcc (0 : ℝ) T hT τ)) (b (z,t)) (Icc (0 : ℝ) T) (t : ℝ))
    (x : M.Carrier) (t : Time T) :
    HasDerivWithinAt (fun τ => localizedTerm P T p v (x,projIcc (0 : ℝ) T hT τ))
      (localizedTerm P T p b (x,t)) (Icc (0 : ℝ) T) (t : ℝ) := by
  by_cases hx : x ∈ P.charts.chart p '' closedBall 0 P.radius
  · have hz := (inverseChart_mem_of_cover P p hx).2
    have hz' : (P.charts.chart p).symm x ∈ ball (0 : ComplexVector n) (2*P.radius) :=
      mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz) (by have := P.radius_pos; linarith))
    exact (hv _ hz' t).const_mul (P.localization p x)
  · have heq : (fun τ => localizedTerm P T p v (x,projIcc (0 : ℝ) T hT τ)) = (fun _ => 0) :=
      funext (fun τ => localizedTerm_zero_of_not_cover P T p v _ hx)
    rw [heq,localizedTerm_zero_of_not_cover P T p b (x,t) hx]
    exact hasDerivWithinAt_const _ _ _

def globalSum (P : UniformChartPartition g) (T : ℝ)
    (v : P.centers → ComplexVector n × Time T → ℝ) (q : Cylinder M T) : ℝ :=
  ∑ᶠ p, localizedTerm P T p (v p) q

theorem globalSum_continuous (P : UniformChartPartition g) (T : ℝ)
    (v : P.centers → ComplexVector n × Time T → ℝ)
    (hv : ∀ p, ContinuousOn (v p) (ball (0 : ComplexVector n) (2*P.radius) ×ˢ (Set.univ : Set (Time T)))) :
    Continuous (globalSum P T v) :=
  continuous_supported_finsum P T (fun p => localizedTerm P T p (v p))
    (fun p => localizedTerm_continuous P T p (v p) (hv p))
    (fun p q hq => localizedTerm_zero_of_not_cover P T p (v p) q hq)

theorem globalSum_initial (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    (v : P.centers → ComplexVector n × Time T → ℝ)
    (hv : ∀ p z, z ∈ ball (0 : ComplexVector n) (2*P.radius) → v p (z,⟨0,⟨le_rfl,hT⟩⟩) = 0)
    (x : M.Carrier) : globalSum P T v (x,⟨0,⟨le_rfl,hT⟩⟩) = 0 := by
  simp only [globalSum,localizedTerm_initial P T hT _ _ (hv _),finsum_zero]

theorem globalSum_hasDerivWithinAt (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    (v b : P.centers → ComplexVector n × Time T → ℝ)
    (hv : ∀ p z, z ∈ ball (0 : ComplexVector n) (2*P.radius) → ∀ t : Time T,
      HasDerivWithinAt (fun τ => v p (z,projIcc (0 : ℝ) T hT τ)) (b p (z,t)) (Icc (0 : ℝ) T) (t : ℝ))
    (x : M.Carrier) (t : Time T) :
    HasDerivWithinAt (fun τ => globalSum P T v (x,projIcc (0 : ℝ) T hT τ))
      (globalSum P T b (x,t)) (Icc (0 : ℝ) T) (t : ℝ) := by
  obtain ⟨I,hI,hActive⟩ := exists_active_finset P x
  exact hasDerivWithinAt_finsum
    (fun p τ => localizedTerm P T p (v p) (x,projIcc (0 : ℝ) T hT τ))
    (fun p => localizedTerm P T p (b p) (x,t)) I _ _
    (fun p _ => localizedTerm_hasDerivWithinAt P T hT p (v p) (b p) (hv p) x t)
    (fun τ p hp => localizedTerm_zero_of_not_cover P T p (v p) _ (hActive p hp))
    (fun p hp => localizedTerm_zero_of_not_cover P T p (b p) _ (hActive p hp))

end Yau.LeafProofs.L17LocalizedSchauderAux
