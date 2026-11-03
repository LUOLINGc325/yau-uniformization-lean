import Yau.LeafProofs.L22Strictifier
import Yau.LeafProofs.L22PatchingSmooth
import Yau.LeafProofs.L22LeviTransport

noncomputable section

open scoped Topology ContDiff Manifold Matrix ComplexOrder
open Set Filter

namespace Yau.LeafProofs.L22Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- The local branches are constructed from the original classical input,
the actual smooth bump covering, and the proved local convolution theorem. -/
theorem exists_strict_branch_cover (u ε : M.Carrier → ℝ)
    (hu : LeafCandidates.ClassicalStrictPsh u) (hε : Continuous ε) (hεpos : ∀ x, 0 < ε x) :
    ∃ (ι : Type) (χ : ι → M.Carrier → ℝ) (δ : ι → ℝ)
      (g : ι → M.Carrier → ℝ) (W : ι → Set M.Carrier),
      LocallyFinite (fun i => tsupport (χ i)) ∧ (∀ i, 0 < δ i) ∧
      (∀ i, IsOpen (W i)) ∧ (∀ i, tsupport (χ i) ⊆ W i) ∧
      (∀ x, ∃ j, χ j =ᶠ[𝓝 x] (fun _ => 1)) ∧
      (∀ i x, x ∈ W i → ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) ∞ (g i) x) ∧
      (∀ i x, x ∈ W i → (levi (g i) x).PosDef) ∧
      (∀ i x, x ∈ W i → χ i x = 1 → u x + 6 * δ i < g i x) ∧
      (∀ i x, x ∈ W i → χ i x = 0 → g i x < u x - 6 * δ i) ∧
      ∀ i x, x ∈ W i → g i x + δ i < u x + ε x := by
  classical
  letI := L12Aux.manifold_realSmooth M
  letI : LocallyCompactSpace M.Carrier := L12Aux.manifold_locallyCompact M
  choose r lam τ hr hlam htarget hτ hpsh hlower using
    (fun p : M.Carrier => exists_classical_strictifier_ball hu p)
  let U : M.Carrier → Set M.Carrier := fun p =>
    (extChartAt (ComplexModel n) p).source ∩
      (chartPt p) ⁻¹' Metric.ball (chartPt p p) (r p)
  have hU (p : M.Carrier) : U p ∈ 𝓝 p := by
    apply (isOpen_extChartAt_preimage' (I := ComplexModel n) p Metric.isOpen_ball).mem_nhds
    exact ⟨mem_extChartAt_source p, Metric.mem_ball_self (hr p)⟩
  obtain ⟨ι, χ, hsub⟩ := SmoothBumpCovering.exists_isSubordinate
    (I := 𝓘(ℝ, ComplexVector n)) (s := (univ : Set M.Carrier)) isClosed_univ
    (fun p _ => hU p)
  have hlocal (i : ι) : ∃ (t : ℝ) (W : Set M.Carrier) (g : M.Carrier → ℝ),
      0 < t ∧ IsOpen W ∧ tsupport (χ i) ⊆ W ∧
      (∀ x ∈ W, ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) ∞ g x) ∧
      (∀ x ∈ W, (levi g x).PosDef) ∧
      (∀ x ∈ W, |g x - u x - t * (2 * χ i x - 1)| < t / 4) ∧
      ∀ x ∈ W, 2 * t < ε x := by
    let p := χ.c i
    let K : Set (ComplexVector n) := chartPt p '' tsupport (χ i)
    have hsource : tsupport (χ i) ⊆ (extChartAt (ComplexModel n) p).source :=
      fun x hx => (hsub i hx).1
    have hK : IsCompact K := (χ i).hasCompactSupport.image_of_continuousOn
      ((continuousOn_extChartAt (I := ComplexModel n) p).mono hsource)
    have hKr : K ⊆ Metric.ball (chartPt p p) (r p) := by
      rintro z ⟨x, hx, rfl⟩
      exact (hsub i hx).2
    have hsmalltarget : Metric.closedBall (chartPt p p) (2 * r p) ⊆ chartTarget p :=
      (Metric.closedBall_subset_closedBall (by linarith [hr p])).trans (htarget p)
    have hbigTarget : Metric.ball (chartPt p p) (3 * r p) ⊆ chartTarget p :=
      Metric.ball_subset_closedBall.trans (htarget p)
    have hχs : ContDiffOn ℝ ∞ (inChart p (χ i)) (Metric.ball (chartPt p p) (3 * r p)) :=
      (L18Aux.smoothFn_of_contMDiff_real (χ i).contMDiff p).mono hbigTarget
    have hεc : ContinuousOn (inChart p ε) (Metric.closedBall (chartPt p p) (2 * r p)) :=
      hε.comp_continuousOn ((continuousOn_extChartAt_symm (I := ComplexModel n) p).mono hsmalltarget)
    obtain ⟨t, V, h, ht, hV, hKV, hVsmall, hhs, hhpos, hherror, hheps⟩ :=
      exists_coordinate_strict_branch (chartPt p p) (hr p) (hlam p)
        (inChart p u) (τ p) (inChart p (χ i)) (inChart p ε)
        (hτ p) hχs (hpsh p) (hlower p) hεc (fun z _ => hεpos (chartInv p z)) hK hKr
    let W : Set M.Carrier := (extChartAt (ComplexModel n) p).source ∩ (chartPt p) ⁻¹' V
    let g : M.Carrier → ℝ := fun x => h (chartPt p x)
    refine ⟨t, W, g, ht,
      isOpen_extChartAt_preimage' (I := ComplexModel n) p hV,
      (fun x hx => ⟨hsource hx, hKV (mem_image_of_mem (chartPt p) hx)⟩), ?_, ?_, ?_, ?_⟩
    · intro x hx
      have hrealSource : x ∈ (extChartAt 𝓘(ℝ, ComplexVector n) p).source := by
        simpa only [L12Aux.real_extChartAt_eq] using hx.1
      have hchart : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) ∞ (chartPt p) x := by
        simpa only [chartPt, L12Aux.real_extChartAt_eq] using!
          (contMDiffAt_extChartAt' (I := 𝓘(ℝ, ComplexVector n)) (n := ∞)
            (by simpa only [extChartAt_source] using hrealSource))
      exact (hhs.contDiffAt (hV.mem_nhds hx.2)).comp_contMDiffAt hchart
    · intro x hx
      exact levi_posDef_chart_branch p x hx.1
        ((hhs.contDiffAt (hV.mem_nhds hx.2)).of_le (by simp)) (hhpos _ hx.2)
    · intro x hx
      have hleft : chartInv p (chartPt p x) = x :=
        (extChartAt (ComplexModel n) p).left_inv hx.1
      simpa only [inChart, hleft] using hherror (chartPt p x) hx.2
    · intro x hx
      have hleft : chartInv p (chartPt p x) = x :=
        (extChartAt (ComplexModel n) p).left_inv hx.1
      simpa only [inChart, hleft] using hheps (chartPt p x) hx.2
  choose t W g ht hW hsupp hgs hgpos herr heps using hlocal
  refine ⟨ι, (fun i => χ i), (fun i => t i / 8), g, W, χ.locallyFinite.closure,
    (fun i => div_pos (ht i) (by norm_num)), hW, hsupp,
    (fun x => ⟨χ.ind x (mem_univ x), χ.eventuallyEq_one x (mem_univ x)⟩),
    hgs, hgpos, ?_, ?_, ?_⟩
  · intro i x hx hχx
    change χ i x = 1 at hχx
    have h := (abs_lt.mp (herr i x hx)).1
    rw [hχx] at h
    linarith
  · intro i x hx hχx
    change χ i x = 0 at hχx
    have h := (abs_lt.mp (herr i x hx)).2
    rw [hχx] at h
    linarith
  · intro i x hx
    have h := (abs_lt.mp (herr i x hx)).2
    have hχle : χ i x ≤ 1 := (χ i).le_one
    have hmul : t i * (2 * χ i x - 1) ≤ t i :=
      mul_le_of_le_one_right (ht i).le (by linarith)
    linarith [heps i x hx, ht i]

end Yau.LeafProofs.L22Aux
