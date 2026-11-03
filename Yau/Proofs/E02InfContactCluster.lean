import Yau.Proofs.E02CompactEpiGap

open Set Filter
open scoped Topology InnerProductSpace
noncomputable section
namespace Yau.NodeProofs.E02Aux

variable {E D : Type*} [NormedAddCommGroup E] [NormedAddCommGroup D]

/-- Every converging sequence of actual approximate contacts lands in
the zero set of the original product gap, by the proved epigraph estimate. -/
theorem compactInfConvolution_cluster_zero {m : ℕ}
    (K : Set E) (v : E → ℝ) (hK : IsCompact K) (hne : K.Nonempty)
    (hv : LowerSemicontinuousOn v K) (hv0 : ∀ a ∈ K, 0 ≤ v a)
    (S : Set D) (π : Fin m → D → E) (hπ : ∀ i, Continuous (π i))
    (hπK : ∀ Q ∈ S, ∀ i, π i Q ∈ K)
    {M : ℝ} (hM : 0 ≤ M) (hπM : ∀ Q ∈ S, ∀ i, v (π i Q) ≤ M)
    (α : Fin m → ℝ) (hα : ∀ i, 0 ≤ α i)
    (g : D → ℝ) (hg : ContinuousOn g S)
    (hNonneg : ∀ Q ∈ S, 0 ≤ (∑ i, α i*v (π i Q))-g Q)
    (κ : ℕ → ℝ) (hκ : ∀ j, 0 < κ j) (hκlim : Tendsto κ atTop (𝓝 0))
    (Q : ℕ → D) (Q₀ : D) (hQ : ∀ j, Q j ∈ S) (hQ₀ : Q₀ ∈ S)
    (hQLim : Tendsto Q atTop (𝓝 Q₀)) (c : ℕ → ℝ) (hc : Tendsto c atTop (𝓝 0))
    (hUpper : ∀ j, (∑ i, α i*compactInfConvolution K v (κ j) (π i (Q j)))-g (Q j) ≤ c j) :
    (∑ i, α i*v (π i Q₀))-g Q₀ = 0 := by
  apply le_antisymm _ (hNonneg Q₀ hQ₀)
  by_contra h
  have hPos : 0 < (∑ i, α i*v (π i Q₀))-g Q₀ := lt_of_not_ge h
  let r := ((∑ i, α i*v (π i Q₀))-g Q₀)/2
  have hr : 0 < r := by dsimp [r]; linarith
  have hrGap : r < (∑ i, α i*v (π i Q₀))-g Q₀ := by dsimp [r]; linarith
  have hLower := compactInfConvolution_weighted_lower_limit K v hK hne hv hv0 S π hπ hπK
    hM hπM α hα g hg κ hκ hκlim Q Q₀ hQ hQ₀ hQLim r hrGap
  have hSmall : ∀ᶠ j in atTop, c j < r := hc.eventually (Iio_mem_nhds hr)
  obtain ⟨j,hj,hcj⟩ := (hLower.and hSmall).exists
  have hUpperj := hUpper j
  linarith

theorem compactInfConvolution_affine_minimizer_cluster_zero [InnerProductSpace ℝ D] {m : ℕ}
    (K : Set E) (v : E → ℝ) (hK : IsCompact K) (hne : K.Nonempty)
    (hv : LowerSemicontinuousOn v K) (hv0 : ∀ a ∈ K, 0 ≤ v a)
    (S : Set D) (π : Fin m → D → E) (hπ : ∀ i, Continuous (π i))
    (hπK : ∀ Q ∈ S, ∀ i, π i Q ∈ K)
    {M : ℝ} (hM : 0 ≤ M) (hπM : ∀ Q ∈ S, ∀ i, v (π i Q) ≤ M)
    (α : Fin m → ℝ) (hα : ∀ i, 0 ≤ α i)
    (g : D → ℝ) (hg : ContinuousOn g S)
    (hNonneg : ∀ Q ∈ S, 0 ≤ (∑ i, α i*v (π i Q))-g Q)
    (κ : ℕ → ℝ) (hκ : ∀ j, 0 < κ j) (hκlim : Tendsto κ atTop (𝓝 0))
    (Q : ℕ → D) (Q₀ Qstar : D) (hQ : ∀ j, Q j ∈ S) (hQ₀ : Q₀ ∈ S) (hQstar : Qstar ∈ S)
    (hQLim : Tendsto Q atTop (𝓝 Q₀)) (p : ℕ → D) (hp : Tendsto p atTop (𝓝 0))
    (hCenter : ∀ j, (∑ i, α i*compactInfConvolution K v (κ j) (π i Qstar))-g Qstar ≤ 0)
    (hMin : ∀ j, ∀ R ∈ S,
      ((∑ i, α i*compactInfConvolution K v (κ j) (π i (Q j)))-g (Q j))-⟪p j,Q j⟫_ℝ ≤
      ((∑ i, α i*compactInfConvolution K v (κ j) (π i R))-g R)-⟪p j,R⟫_ℝ) :
    (∑ i, α i*v (π i Q₀))-g Q₀ = 0 := by
  have hTilt : Tendsto (fun j => ⟪p j,Q j-Qstar⟫_ℝ) atTop (𝓝 0) := by
    simpa only [inner_zero_left] using hp.inner (hQLim.sub tendsto_const_nhds)
  have hUpper : ∀ j,
      (∑ i, α i*compactInfConvolution K v (κ j) (π i (Q j)))-g (Q j) ≤ ⟪p j,Q j-Qstar⟫_ℝ := by
    intro j
    have hm := hMin j Qstar hQstar
    have hc := hCenter j
    rw [inner_sub_right]
    linarith
  exact compactInfConvolution_cluster_zero K v hK hne hv hv0 S π hπ hπK hM hπM α hα g hg
    hNonneg κ hκ hκlim Q Q₀ hQ hQ₀ hQLim (fun j => ⟪p j,Q j-Qstar⟫_ℝ) hTilt hUpper

end Yau.NodeProofs.E02Aux
