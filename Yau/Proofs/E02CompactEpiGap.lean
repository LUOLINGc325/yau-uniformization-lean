import Yau.Proofs.E02FiniteEpiLower

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.NodeProofs.E02Aux

variable {E D : Type*} [NormedAddCommGroup E] [NormedAddCommGroup D]

theorem compactInfConvolution_weighted_lower_limit {m : ℕ}
    (K : Set E) (v : E → ℝ) (hK : IsCompact K) (hne : K.Nonempty)
    (hv : LowerSemicontinuousOn v K) (hv0 : ∀ a ∈ K, 0 ≤ v a)
    (S : Set D) (π : Fin m → D → E) (hπ : ∀ i, Continuous (π i))
    (hπK : ∀ Q ∈ S, ∀ i, π i Q ∈ K)
    {M : ℝ} (hM : 0 ≤ M) (hπM : ∀ Q ∈ S, ∀ i, v (π i Q) ≤ M)
    (α : Fin m → ℝ) (hα : ∀ i, 0 ≤ α i)
    (g : D → ℝ) (hg : ContinuousOn g S)
    (κ : ℕ → ℝ) (hκ : ∀ j, 0 < κ j) (hκlim : Tendsto κ atTop (𝓝 0))
    (Q : ℕ → D) (Q₀ : D) (hQ : ∀ j, Q j ∈ S) (hQ₀ : Q₀ ∈ S)
    (hQLim : Tendsto Q atTop (𝓝 Q₀)) :
    ∀ r < (∑ i, α i*v (π i Q₀))-g Q₀,
      ∀ᶠ j in atTop, r ≤ (∑ i, α i*compactInfConvolution K v (κ j) (π i (Q j)))-g (Q j) := by
  have hLower : ∀ i, ∀ r < v (π i Q₀),
      ∀ᶠ j in atTop, r ≤ compactInfConvolution K v (κ j) (π i (Q j)) := by
    intro i
    exact compactInfConvolution_lower_limit K v hK hne hv hv0 κ hκ hκlim hM
      (fun j => π i (Q j)) (π i Q₀) (hπK Q₀ hQ₀ i)
      (fun j => hπK (Q j) (hQ j) i) (fun j => hπM (Q j) (hQ j) i)
      ((hπ i).continuousAt.tendsto.comp hQLim)
  have hWithin : Tendsto Q atTop (𝓝[S] Q₀) :=
    tendsto_nhdsWithin_iff.mpr ⟨hQLim,Eventually.of_forall hQ⟩
  have hgLim : Tendsto (fun j => g (Q j)) atTop (𝓝 (g Q₀)) :=
    (hg Q₀ hQ₀).tendsto.comp hWithin
  exact finite_weighted_epigraph_lower_sub_tendsto α hα
    (fun i j => compactInfConvolution K v (κ j) (π i (Q j)))
    (fun i => v (π i Q₀)) hLower (fun j => g (Q j)) (g Q₀) hgLim

/-- A positive gap on an actual compact boundary persists uniformly for
the compact-source inf-convolutions. K and M precede every kappa limit. -/
theorem compactInfConvolution_uniform_gap {m : ℕ}
    (K : Set E) (v : E → ℝ) (hK : IsCompact K) (hne : K.Nonempty)
    (hv : LowerSemicontinuousOn v K) (hv0 : ∀ a ∈ K, 0 ≤ v a)
    (S : Set D) (hS : IsCompact S) (π : Fin m → D → E) (hπ : ∀ i, Continuous (π i))
    (hπK : ∀ Q ∈ S, ∀ i, π i Q ∈ K)
    {M : ℝ} (hM : 0 ≤ M) (hπM : ∀ Q ∈ S, ∀ i, v (π i Q) ≤ M)
    (α : Fin m → ℝ) (hα : ∀ i, 0 ≤ α i)
    (g : D → ℝ) (hg : ContinuousOn g S)
    (κ : ℕ → ℝ) (hκ : ∀ j, 0 < κ j) (hκlim : Tendsto κ atTop (𝓝 0))
    {γ δ : ℝ} (hδ : δ < γ)
    (hGap : ∀ Q ∈ S, γ ≤ (∑ i, α i*v (π i Q))-g Q) :
    ∀ᶠ j in atTop, ∀ Q ∈ S,
      δ ≤ (∑ i, α i*compactInfConvolution K v (κ j) (π i Q))-g Q := by
  by_contra hEvent
  have hFreq : ∃ᶠ j in atTop, ∃ Q ∈ S,
      (∑ i, α i*compactInfConvolution K v (κ j) (π i Q))-g Q < δ := by
    simpa only [not_eventually,not_forall,not_le,exists_prop] using hEvent
  obtain ⟨φ,hφ,hBadφ⟩ := extraction_of_frequently_atTop hFreq
  choose Q hQS hBad using hBadφ
  obtain ⟨Q₀,hQ₀,ψ,hψ,hQLim⟩ := hS.isSeqCompact hQS
  have hSubκ : Tendsto (fun j => κ (φ (ψ j))) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using hκlim.comp (hφ.comp hψ).tendsto_atTop
  have hLower := compactInfConvolution_weighted_lower_limit K v hK hne hv hv0 S π hπ hπK
    hM hπM α hα g hg (fun j => κ (φ (ψ j))) (fun j => hκ (φ (ψ j))) hSubκ
    (fun j => Q (ψ j)) Q₀ (fun j => hQS (ψ j)) hQ₀ hQLim
    ((δ+γ)/2) (by linarith [hGap Q₀ hQ₀])
  obtain ⟨j,hj⟩ := hLower.exists
  have hBadj := hBad (ψ j)
  linarith

end Yau.NodeProofs.E02Aux
