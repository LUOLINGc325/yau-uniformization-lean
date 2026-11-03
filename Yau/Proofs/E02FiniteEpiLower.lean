import Yau.Proofs.E02InfEpiConvergence

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.NodeProofs.E02Aux

/-- Positive finite sums preserve the actual eventual lower bounds.
The estimate also includes an empty contact list. -/
theorem finite_weighted_epigraph_lower {m : ℕ} (α : Fin m → ℝ)
    (hα : ∀ i, 0 ≤ α i) (f : Fin m → ℕ → ℝ) (v : Fin m → ℝ)
    (hLower : ∀ i, ∀ r < v i, ∀ᶠ j in atTop, r ≤ f i j) :
    ∀ r < ∑ i, α i*v i, ∀ᶠ j in atTop, r ≤ ∑ i, α i*f i j := by
  intro r hr
  let A := ∑ i, α i
  let s := ∑ i, α i*v i
  let δ := (s-r)/(2*(A+1))
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ => hα i)
  have hδ : 0 < δ := div_pos (sub_pos.mpr hr) (by positivity)
  have hδEq : δ*(2*(A+1)) = s-r := div_mul_cancel₀ _ (by positivity)
  have hAll : ∀ᶠ j in atTop, ∀ i : Fin m, v i-δ ≤ f i j :=
    eventually_all.2 (fun i => hLower i (v i-δ) (by linarith))
  filter_upwards [hAll] with j hj
  have hSum : ∑ i, α i*(v i-δ) ≤ ∑ i, α i*f i j :=
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hj i) (hα i))
  have hExpand : ∑ i, α i*(v i-δ) = s-δ*A := by
    simp only [mul_sub,Finset.sum_sub_distrib]
    dsimp [s,A]
    rw [←Finset.sum_mul]
    ring
  rw [hExpand] at hSum
  have hδA : 0 ≤ δ*A := mul_nonneg hδ.le hA
  nlinarith

theorem finite_weighted_epigraph_lower_sub_tendsto {m : ℕ} (α : Fin m → ℝ)
    (hα : ∀ i, 0 ≤ α i) (f : Fin m → ℕ → ℝ) (v : Fin m → ℝ)
    (hLower : ∀ i, ∀ r < v i, ∀ᶠ j in atTop, r ≤ f i j)
    (g : ℕ → ℝ) (g₀ : ℝ) (hg : Tendsto g atTop (𝓝 g₀)) :
    ∀ r < (∑ i, α i*v i)-g₀, ∀ᶠ j in atTop, r ≤ (∑ i, α i*f i j)-g j := by
  intro r hr
  let ε := ((∑ i, α i*v i)-g₀-r)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hThreshold : r+g₀+ε < ∑ i, α i*v i := by dsimp [ε]; linarith
  have hSum := finite_weighted_epigraph_lower α hα f v hLower (r+g₀+ε) hThreshold
  have hG : ∀ᶠ j in atTop, g j < g₀+ε := hg.eventually (Iio_mem_nhds (by linarith))
  filter_upwards [hSum,hG] with j hj hgj
  linarith

end Yau.NodeProofs.E02Aux
