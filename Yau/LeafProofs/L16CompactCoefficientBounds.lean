import Yau.LeafProofs.L16EnergyEquation

open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

/-- C¹ regularity on a compact set bounds the actual derivative on every open
subset of that set. No derivative value or uniqueness is required on its boundary. -/
theorem bounded_fderiv_on_open_subset_of_compact
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K U : Set E} {g : E → F}
    (hK : IsCompact K) (hU : IsOpen U) (hUK : U ⊆ K)
    (hg : ContDiffOn ℝ 1 g K) :
    ∃ A : ℝ, 0 < A ∧ ∀ p ∈ U, ‖fderiv ℝ g p‖ ≤ A := by
  classical
  have hLocal (x : K) : ∃ V : Set E, IsOpen V ∧ (x : E) ∈ V ∧
      ∃ C : ℝ, 0 < C ∧ ∀ y ∈ V, y ∈ U → ‖fderiv ℝ g y‖ ≤ C := by
    obtain ⟨u, hu, hus, han, g', hder, hcont⟩ :=
      (contDiffWithinAt_succ_iff_hasFDerivWithinAt' (𝕜 := ℝ) (n := 0) (by simp)).mp
        (by simpa using hg x x.property)
    rw [insert_eq_of_mem x.property] at hu
    have hc : ContinuousWithinAt g' K x := hcont.continuousWithinAt
    have hnorm : ∀ᶠ y in 𝓝[K] (x : E), ‖g' y‖ < ‖g' x‖ + 1 :=
      hc.norm.eventually (gt_mem_nhds (lt_add_one ‖g' x‖))
    obtain ⟨V, hV, hxV, hVu⟩ := mem_nhdsWithin.mp (inter_mem hu hnorm)
    refine ⟨V, hV, hxV, ‖g' x‖ + 1, by positivity, ?_⟩
    intro y hyV hyU
    have hy := hVu ⟨hyV, hUK hyU⟩
    have hEq : fderiv ℝ g y = g' y :=
      ((hder y hy.1).hasFDerivAt (Filter.mem_of_superset (hU.mem_nhds hyU) hUK)).fderiv
    rw [hEq]
    exact hy.2.le
  choose V hV hxV C hC hBound using hLocal
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover V hV (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩, hxV ⟨x,hx⟩⟩)
  have hsum : 0 ≤ ∑ x ∈ s, C x := Finset.sum_nonneg (fun x _ => (hC x).le)
  refine ⟨1 + ∑ x ∈ s, C x, by linarith, ?_⟩
  intro p hp
  obtain ⟨x, hxs, hpx⟩ := mem_iUnion₂.mp (hs (hUK hp))
  have hle : C x ≤ ∑ y ∈ s, C y := Finset.single_le_sum (fun y _ => (hC y).le) hxs
  exact (hBound x p hpx hp).trans (by linarith)

/-- On an interior point the actual spatial matrix-entry derivative is the
corresponding component of the actual joint derivative. -/
theorem coefficient_spatial_derivative_eq_joint {n : ℕ}
    {a : Point n → Mat n} {p : Point n} (ha : DifferentiableAt ℝ a p)
    (i j : Yau.RIdx n) :
    d (fun x => a (x,p.2) i j) p.1 i =
      (fderiv ℝ a p (Yau.realVec i,0)) i j := by
  have hArg : HasFDerivAt (fun x : Space n => (x,p.2))
      ((ContinuousLinearMap.id ℝ (Space n)).prod (0 : Space n →L[ℝ] ℝ)) p.1 :=
    (hasFDerivAt_id p.1).prodMk (hasFDerivAt_const p.2 p.1)
  have h := congrArg (fun L : Space n →L[ℝ] ℝ => L (Yau.realVec i))
    ((((matrixEntryCLM i j).hasFDerivAt.comp p ha.hasFDerivAt).comp p.1 hArg).fderiv)
  exact h

/-- The frozen closed-cylinder smoothness hypothesis supplies all coefficient
bounds needed by the energy form, with constants chosen before any forcing. -/
theorem smoothDomain_compact_coefficient_bounds {n : ℕ} {O : Set (Space n)}
    (hO : SmoothDomain O) {T : ℝ} (_hT : 0 < T)
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hSmooth : SmoothCoefficients (cylinder (closure O) 0 T) a b) :
    ∃ A D : ℝ, 0 < A ∧ 0 < D ∧
      (∀ p ∈ O ×ˢ Ioo 0 T, ∀ i j, |a p i j| ≤ A) ∧
      ∀ p ∈ O ×ˢ Ioo 0 T, ∑ j, |energyDrift a b p j|^2 ≤ D^2 := by
  classical
  let K : Set (Point n) := cylinder (closure O) 0 T
  let U : Set (Point n) := O ×ˢ Ioo 0 T
  have hK : IsCompact K := hO.2.2.1.prod isCompact_Icc
  have hU : IsOpen U := hO.1.prod isOpen_Ioo
  have hUK : U ⊆ K := by
    intro p hp
    exact ⟨subset_closure hp.1, Ioo_subset_Icc_self hp.2⟩
  obtain ⟨A₀,hA₀⟩ := hK.exists_bound_of_continuousOn hSmooth.1.continuousOn
  obtain ⟨L,hL,hDeriv⟩ := bounded_fderiv_on_open_subset_of_compact hK hU hUK
    (hSmooth.1.of_le (by simp))
  have hEachB (j : Yau.RIdx n) : ∃ C : ℝ, ∀ p ∈ K, |b p j| ≤ C := by
    simpa only [Real.norm_eq_abs] using
      hK.exists_bound_of_continuousOn (hSmooth.2 j).continuousOn
  choose C hC using hEachB
  let B : ℝ := 1 + ∑ j, |C j|
  have hB : 0 < B := by dsimp only [B]; positivity
  have hBoundB : ∀ p ∈ U, ∀ j, |b p j| ≤ B := by
    intro p hp j
    have hCj : |C j| ≤ ∑ k, |C k| := Finset.single_le_sum (fun k _ => abs_nonneg (C k)) (Finset.mem_univ j)
    exact (hC j p (hUK hp)).trans (by dsimp only [B]; linarith [le_abs_self (C j)])
  have hSpatial : ∀ p ∈ U, ∀ i j,
      |d (fun x => a (x,p.2) i j) p.1 i| ≤ L := by
    intro p hp i j
    have ha : DifferentiableAt ℝ a p :=
      ((hSmooth.1.mono hUK).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
    rw [coefficient_spatial_derivative_eq_joint ha]
    have hNorm : ‖(Yau.realVec i, (0 : ℝ))‖ = 1 := by
      simp only [Prod.norm_def, realVec_norm, norm_zero, max_eq_left (by norm_num : (0 : ℝ) ≤ 1)]
    exact (frobenius_entry_abs_le _ i j).trans
      (((fderiv ℝ a p).le_opNorm _).trans (by rw [hNorm, mul_one]; exact hDeriv p hp))
  let M : ℝ := B + ∑ _i : Yau.RIdx n, L
  have hM : 0 < M := by
    dsimp only [M]
    exact add_pos_of_pos_of_nonneg hB (Finset.sum_nonneg (fun _ _ => hL.le))
  have hDrift : ∀ p ∈ U, ∀ j, |energyDrift a b p j| ≤ M := by
    intro p hp j
    calc
      |energyDrift a b p j| ≤ |b p j| + |∑ i, d (fun x => a (x,p.2) i j) p.1 i| := abs_sub _ _
      _ ≤ B + ∑ _i : Yau.RIdx n, L := add_le_add (hBoundB p hp j)
        ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => hSpatial p hp i j)))
  let D : ℝ := 1 + ∑ _j : Yau.RIdx n, M
  have hD : 0 < D := by
    dsimp only [D]
    exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun _ _ => hM.le))
  refine ⟨1+|A₀|, D, by positivity, hD, ?_, ?_⟩
  · intro p hp i j
    exact (frobenius_entry_abs_le _ i j).trans
      ((hA₀ p (hUK hp)).trans (by linarith [le_abs_self A₀]))
  · intro p hp
    have hSum : ∑ j, |energyDrift a b p j| ≤ D := by
      exact (Finset.sum_le_sum (fun j _ => hDrift p hp j)).trans
        (by dsimp only [D]; linarith)
    exact (Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => abs_nonneg (energyDrift a b p j))).trans
      (sq_le_sq₀ (Finset.sum_nonneg (fun j _ => abs_nonneg (energyDrift a b p j))) hD.le |>.mpr hSum)

/-- Actual coefficient entries and actual energy drift are measurable on the
open slab and on every interior time section. -/
theorem smooth_coefficients_energyDrift_aestronglyMeasurable {n : ℕ}
    {O : Set (Space n)} (hO : IsOpen O) {T : ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hSmooth : SmoothCoefficients (cylinder (closure O) 0 T) a b) :
    (∀ i j, AEStronglyMeasurable (fun p => a p i j)
      (productVolume O (Ioo 0 T))) ∧
    (∀ j, AEStronglyMeasurable (fun p => energyDrift a b p j)
      (productVolume O (Ioo 0 T))) ∧
    ∀ t ∈ Ioo 0 T,
      (∀ i j, AEStronglyMeasurable (fun x => a (x,t) i j)
        (volume.restrict O)) ∧
      ∀ j, AEStronglyMeasurable (fun x => energyDrift a b (x,t) j)
        (volume.restrict O) := by
  let U : Set (Point n) := O ×ˢ Ioo 0 T
  have hU : IsOpen U := hO.prod isOpen_Ioo
  have hUK : U ⊆ cylinder (closure O) 0 T := by
    intro p hp
    exact ⟨subset_closure hp.1, Ioo_subset_Icc_self hp.2⟩
  have hSmoothU : SmoothCoefficients U a b :=
    ⟨hSmooth.1.mono hUK, fun j => (hSmooth.2 j).mono hUK⟩
  have ha (i j : Yau.RIdx n) : ContinuousOn (fun p => a p i j) U :=
    ((matrixEntryCLM i j).contDiff.comp_contDiffOn hSmoothU.1).continuousOn
  have hd (j : Yau.RIdx n) : ContinuousOn (fun p => energyDrift a b p j) U :=
    (energyDrift_smooth hU hSmoothU j).continuousOn
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    rw [productVolume_eq_restrict]
    exact (ha i j).aestronglyMeasurable hU.measurableSet
  · intro j
    rw [productVolume_eq_restrict]
    exact (hd j).aestronglyMeasurable hU.measurableSet
  · intro t ht
    have hSlice : ContinuousOn (fun x : Space n => (x,t)) O :=
      (continuous_id.prodMk continuous_const).continuousOn
    have hMap : MapsTo (fun x : Space n => (x,t)) O U := fun x hx => ⟨hx,ht⟩
    exact ⟨fun i j => ((ha i j).comp hSlice hMap).aestronglyMeasurable hO.measurableSet,
      fun j => ((hd j).comp hSlice hMap).aestronglyMeasurable hO.measurableSet⟩

end Yau.LeafProofs.L16Aux
