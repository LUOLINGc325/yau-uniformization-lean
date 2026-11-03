import Yau.Proofs.D04RepresentativeClass

open MeasureTheory Filter Set
open scoped Topology ContDiff

noncomputable section

namespace Yau.Proofs.D04Aux

open Yau Yau.Blueprint

variable {n : ℕ}

/-- A strict bound on the same-class representative gives a uniform
eventual bound for the original sequence on a real neighborhood. -/
theorem eventually_locally_lt_of_uscRepresentative_lt
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    {u : ℕ → ComplexVector n → EReal}
    (hu : ∀ j, IsPshOn (u j) O ∧ CoordinateLocallyL1 O (u j))
    {f : ComplexVector n → ℝ}
    (hf : ∀ S : Set (ComplexVector n), IsCompact S → S ⊆ O → IntegrableOn f S volume)
    (hconv : ∀ S : Set (ComplexVector n), IsCompact S → S ⊆ O →
      Tendsto (fun j => ∫ y in S, |(u j y).toReal - f y|) atTop (𝓝 0))
    {x : ComplexVector n} {a : ℝ} (hxa : uscRepresentative O f x < (a : EReal)) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall x r ⊆ O ∧
      ∀ᶠ j in atTop, ∀ y ∈ Metric.closedBall x r, u j y < (a : EReal) := by
  change (⨅ k : ℕ, radialRegularization O f (natRadius k) x) < (a : EReal) at hxa
  obtain ⟨k, hk⟩ := iInf_lt_iff.mp hxa
  have hD : x ∈ radialDomain O (natRadius k) := by
    by_contra hn
    simp only [radialRegularization, ite_eq_right hn] at hk
    exact (not_top_lt hk).elim
  have hm : (∫ y, radialKernel (natRadius k) (x - y) * f y) < a := by
    apply EReal.coe_lt_coe_iff.mp
    simpa only [radialRegularization, ite_eq_left hD] using hk
  let m : ℝ := ∫ y, radialKernel (natRadius k) (x - y) * f y
  let ε : ℝ := (a - m) / 3
  have hε : 0 < ε := by dsimp only [ε, m]; linarith
  have hfc := (contDiffAt_radialConvolution_local hO hf (natRadius_pos k) hD).continuousAt
  have hsmall : ∀ᶠ y in 𝓝 x,
      y ∈ radialDomain O (natRadius k) ∧
        (∫ z, radialKernel (natRadius k) (y - z) * f z) < m + ε := by
    filter_upwards [(isOpen_radialDomain hO (natRadius k)).mem_nhds hD,
      hfc.eventually (isOpen_Iio.mem_nhds (show m < m + ε by linarith))] with y hyD hy
    exact ⟨hyD, hy⟩
  obtain ⟨r, hr, hnear⟩ := Metric.mem_nhds_iff.mp hsmall
  have hKD : Metric.closedBall x (r / 2) ⊆ radialDomain O (natRadius k) :=
    fun y hy => (hnear ((Metric.closedBall_subset_ball (half_lt_self hr)) hy)).1
  have hKO : Metric.closedBall x (r / 2) ⊆ O := fun y hy =>
    hKD hy (Metric.mem_closedBall_self (mul_nonneg (by norm_num) (natRadius_pos k).le))
  have huni := radialConvolution_uniform_on_compact_of_localL1 (fun j => (hu j).2)
    hf hconv (natRadius_pos k) (isCompact_closedBall x (r / 2)) hKD
  refine ⟨r / 2, half_pos hr, hKO, ?_⟩
  filter_upwards [huni ε hε] with j hj
  intro y hy
  have hfy := (hnear ((Metric.closedBall_subset_ball (half_lt_self hr)) hy)).2
  have hdiff := (abs_lt.mp (hj y hy)).2
  apply (psh_le_radialConvolution (hu j).1 (hu j).2 (natRadius_pos k) (hKD hy)).trans_lt
  apply EReal.coe_lt_coe_iff.mpr
  dsimp only [ε] at *
  linarith

end Yau.Proofs.D04Aux
