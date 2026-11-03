import Yau.Proofs.D02CotangentCompact

/-! Exact compact metric boxes in the induced cotangent atlas. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n : ℕ} {M : ComplexManifold n}

/-- The dual quadratic form scales by the squared scalar norm. -/
theorem dualNormMat_smul (H : Matrix (Fin n) (Fin n) ℂ)
    (c : ℂ) (ξ : ComplexVector n) :
    dualNormMat H (c • ξ) = ‖c‖ ^ 2 * dualNormMat H ξ := by
  have hc : WithLp.ofLp (c • ξ) = c • WithLp.ofLp ξ := rfl
  unfold dualNormMat
  rw [hc, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  rw [← mul_assoc, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Strict positivity holds in every valid chart, including arbitrary metrics. -/
theorem dualNormChart_pos (g : HermitianField M) (x : M.Carrier)
    {z ξ : ComplexVector n} (hz : z ∈ chartTarget x) (hξ : ξ ≠ 0) :
    0 < dualNormChart g x z ξ := by
  apply (Complex.pos_iff.mp
    ((hMat_posDef g x z hz).inv.transpose.dotProduct_mulVec_pos ?_)).1
  intro hzero
  apply hξ
  ext i
  exact congrArg (fun v : Fin n → ℂ => v i) hzero

/-- A common positive coercivity constant on each compact chart base.
The empty unit sphere is allowed, so this also covers dimension zero. -/
theorem dualNormChart_coercive_on_compact
    (g : HermitianField M) (hg : MetricSmooth g) (x : M.Carrier)
    {B : Set (ComplexVector n)} (hB : IsCompact B) (hBt : B ⊆ chartTarget x) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ z ∈ B, ∀ ξ : ComplexVector n,
      lam * ‖ξ‖ ^ 2 ≤ dualNormChart g x z ξ := by
  have hs : IsCompact (B ×ˢ Metric.sphere (0 : ComplexVector n) 1) :=
    hB.prod (isCompact_sphere _ _)
  have hsub : B ×ˢ Metric.sphere (0 : ComplexVector n) 1 ⊆ cotangentTarget x :=
    fun p hp => ⟨hBt hp.1, Set.mem_univ _⟩
  obtain ⟨lam, hlam, hbound⟩ := hs.exists_forall_le'
    ((dualNormChart_contDiffOn_of_metricSmooth g hg x).continuousOn.mono hsub)
    (a := 0) (fun p hp => dualNormChart_pos g x (hBt hp.1) (by
      intro he
      have : ‖p.2‖ = 1 := by simpa using hp.2
      simp [he] at this))
  refine ⟨lam, hlam, fun z hz ξ => ?_⟩
  by_cases hξ : ξ = 0
  · simp [hξ, dualNormChart, dualNormMat]
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  let ξ₁ : ComplexVector n := ((‖ξ‖⁻¹ : ℝ) : ℂ) • ξ
  have hξ₁ : ξ₁ ∈ Metric.sphere (0 : ComplexVector n) 1 := by
    simp [ξ₁, norm_smul, hn.ne']
  have hb := hbound (z, ξ₁) ⟨hz, hξ₁⟩
  have hscale : dualNormChart g x z ξ₁ = ‖ξ‖⁻¹ ^ 2 * dualNormChart g x z ξ := by
    change dualNormMat (hMat g x z) (((‖ξ‖⁻¹ : ℝ) : ℂ) • ξ) = _
    rw [dualNormMat_smul]
    simp [dualNormChart]
  rw [hscale] at hb
  have hm := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖ξ‖)
  have hcancel : (‖ξ‖⁻¹ ^ 2 * dualNormChart g x z ξ) * ‖ξ‖ ^ 2 =
      dualNormChart g x z ξ := by field_simp [hn.ne']
  rwa [hcancel] at hm

/-- The exact quadratic sublevel over a compact valid chart base is compact. -/
theorem isCompact_dualNormChart_sublevel
    (g : HermitianField M) (hg : MetricSmooth g) (x : M.Carrier)
    {B : Set (ComplexVector n)} (hB : IsCompact B) (hBt : B ⊆ chartTarget x) (R : ℝ) :
    IsCompact {p : CotangentCoord n | p.1 ∈ B ∧ dualNormChart g x p.1 p.2 ≤ R} := by
  obtain ⟨lam, hlam, hbound⟩ := dualNormChart_coercive_on_compact g hg x hB hBt
  let T := B ×ˢ Metric.closedBall (0 : ComplexVector n) (Real.sqrt (max R 0 / lam))
  have hT : IsCompact T := hB.prod (isCompact_closedBall _ _)
  have hTs : T ⊆ cotangentTarget x := fun p hp => ⟨hBt hp.1, Set.mem_univ _⟩
  have hcomp : IsCompact {p ∈ T | dualNormChart g x p.1 p.2 ≤ R} :=
    ((dualNormChart_contDiffOn_of_metricSmooth g hg x).continuousOn.mono hTs).lowerSemicontinuousOn.isCompact_inter_preimage_Iic hT R
  convert hcomp using 1
  ext p
  constructor
  · intro hp
    have hb := (hbound p.1 hp.1 p.2).trans hp.2
    have hb' : ‖p.2‖ ^ 2 ≤ max R 0 / lam :=
      (le_div_iff₀ hlam).mpr (by nlinarith [le_max_left R 0])
    exact ⟨⟨hp.1, by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (Real.le_sqrt (norm_nonneg _) (div_nonneg (le_max_right R 0) hlam.le)).mpr hb'⟩,
      hp.2⟩
  · intro hp
    exact ⟨hp.1.1, hp.2⟩


/-- D02.33a, with equality to the original box rather than a compact superset. -/
theorem cotangentBoxCompact : SpliceRepair.CotangentBoxCompact := by
  intro n M g hg K R hK
  classical
  let := Yau.LeafProofs.L12Aux.manifold_locallyCompact M
  have hlocal (x : M.Carrier) : ∃ A : Set M.Carrier, IsCompact A ∧
      x ∈ interior A ∧ A ⊆ (extChartAt (ComplexModel n) x).source :=
    exists_compact_subset (isOpen_extChartAt_source x) (mem_extChartAt_source x)
  choose A hAc hAm hAs using hlocal
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x => interior (A x))
    (fun _ => isOpen_interior) (fun x _ => Set.mem_iUnion.mpr ⟨x, hAm x⟩)
  let J := {a : M.Carrier // a ∈ t}
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let x : Fin (Fintype.card J) → M.Carrier := fun i => (e i).1
  let B : Fin (Fintype.card J) → Set (ComplexVector n) :=
    fun i => chartPt (x i) '' (K ∩ A (x i))
  have hBc (i : Fin (Fintype.card J)) : IsCompact (B i) :=
    (hK.inter_right (hAc (x i)).isClosed).image_of_continuousOn
      ((continuousOn_extChartAt (I := ComplexModel n) (x i)).mono
        (fun y hy => hAs (x i) hy.2))
  have hBt (i : Fin (Fintype.card J)) : B i ⊆ chartTarget (x i) := by
    rintro z ⟨y, hy, rfl⟩
    exact (extChartAt (ComplexModel n) (x i)).map_source (hAs (x i) hy.2)
  let C : Fin (Fintype.card J) → Set (CotangentCoord n) :=
    fun i => {p | p.1 ∈ B i ∧ dualNormChart g (x i) p.1 p.2 ≤ R}
  refine ⟨Fintype.card J, x, C, ?_, ?_⟩
  · intro i
    exact ⟨isCompact_dualNormChart_sublevel g hg (x i) (hBc i) (hBt i) R,
      fun p hp => ⟨hBt i hp.1, Set.mem_univ _⟩⟩
  · ext y
    constructor
    · intro hy
      obtain ⟨a, ha, hya⟩ := Set.mem_iUnion₂.mp (ht hy.1)
      obtain ⟨i, hi⟩ := e.surjective ⟨a, ha⟩
      have hxi : x i = a := congrArg Subtype.val hi
      have hys : y ∈ cotangentSource (x i) := by
        change y.1 ∈ (extChartAt (ComplexModel n) (x i)).source
        rw [hxi]
        exact hAs a (interior_subset hya)
      refine Set.mem_iUnion.mpr ⟨i, cotangentChart (x i) y, ?_,
        cotangentChart_left_inv (x i) hys⟩
      refine ⟨?_, ?_⟩
      · exact ⟨y.1, ⟨hy.1, by rw [hxi]; exact interior_subset hya⟩, rfl⟩
      · change dualNormChart g (x i) (chartPt (x i) y.1)
          (covectorCoords (x i) y.1 y.2) ≤ R
        rw [← dualNorm_eq_fixed_chart g (x i) y.1 hys y.2]
        exact hy.2
    · intro hy
      obtain ⟨i, p, hp, rfl⟩ := Set.mem_iUnion.mp hy
      have hpt : p ∈ cotangentTarget (x i) := ⟨hBt i hp.1, Set.mem_univ _⟩
      refine ⟨?_, ?_⟩
      · obtain ⟨a, ha, hea⟩ := hp.1
        change chartInv (x i) p.1 ∈ K
        rw [← hea]
        have he : chartInv (x i) (chartPt (x i) a) = a :=
          (extChartAt (ComplexModel n) (x i)).left_inv (hAs (x i) ha.2)
        rw [he]
        exact ha.1
      · rw [dualNorm_cotangentChartInv g (x i) hpt]
        exact hp.2

end Yau.NodeProofs.D02Aux
