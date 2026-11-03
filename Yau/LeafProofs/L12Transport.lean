import Yau.LeafProofs.L12Flow

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff Bundle
namespace Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

/-- Two genuine tangent vectors over one base point. -/
abbrev realTransportBundle (M : ComplexManifold n) :=
  Bundle.TotalSpace (ComplexVector n × ComplexVector n)
    ((fun x : M.Carrier => TangentSpace 𝓘(ℝ, ComplexVector n) x) ×ᵇ
      (fun x : M.Carrier => TangentSpace 𝓘(ℝ, ComplexVector n) x))

def realTransportModel (n : ℕ) :=
  𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n × ComplexVector n)

def realTransportDiag (q : realTransportBundle M) :
    (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) ×
      (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :=
  (⟨q.proj, q.2.1⟩, ⟨q.proj, q.2.2⟩)

theorem range_realTransportDiag : Set.range (realTransportDiag (M := M)) =
    {p | p.1.proj = p.2.proj} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    rfl
  · rcases p with ⟨⟨x, v⟩, ⟨y, w⟩⟩
    intro hxy
    change x = y at hxy
    subst y
    exact ⟨⟨x, (v, w)⟩, rfl⟩

/-- Two bounded physical tangent energies over a compact base give a
compact set in the actual Whitney-sum topology. -/
theorem isCompact_realTransportEnergy_sublevel (g : SmoothMetric M)
    {K : Set M.Carrier} (hK : IsCompact K) (A B : ℝ) :
    letI := manifold_realSmooth M
    IsCompact {q : realTransportBundle M | q.proj ∈ K ∧
      realTangentEnergy g.form (realTransportDiag q).1 ≤ A ∧
      realTangentEnergy g.form (realTransportDiag q).2 ≤ B} := by
  letI := manifold_realSmooth M
  have hdiag : Topology.IsInducing (realTransportDiag (M := M)) :=
    FiberBundle.Prod.isInducing_diag
    (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n))
    (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n))
  have hclosed : IsClosed (Set.range (realTransportDiag (M := M))) := by
    rw [range_realTransportDiag]
    exact isClosed_eq
      ((FiberBundle.continuous_proj (ComplexVector n)
        (TangentSpace 𝓘(ℝ, ComplexVector n))).comp continuous_fst)
      ((FiberBundle.continuous_proj (ComplexVector n)
        (TangentSpace 𝓘(ℝ, ComplexVector n))).comp continuous_snd)
  have hprod := (isCompact_realTangentEnergy_sublevel g hK A).prod
    (isCompact_realTangentEnergy_sublevel g hK B)
  have heq : {q : realTransportBundle M | q.proj ∈ K ∧
      realTangentEnergy g.form (realTransportDiag q).1 ≤ A ∧
      realTangentEnergy g.form (realTransportDiag q).2 ≤ B} =
      realTransportDiag ⁻¹' ({p | p.proj ∈ K ∧ realTangentEnergy g.form p ≤ A} ×ˢ
        {p | p.proj ∈ K ∧ realTangentEnergy g.form p ≤ B}) := by
    ext q
    change (_ ∧ _ ∧ _) ↔ ((_ ∧ _) ∧ (_ ∧ _))
    tauto
  rw [heq]
  exact hdiag.isCompact_preimage hclosed hprod

theorem manifold_realTransport (M : ComplexManifold n) :
    letI := manifold_realSmooth M
    IsManifold (realTransportModel n) ∞ (realTransportBundle M) := by
  letI := manifold_realSmooth M
  change IsManifold (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n × ComplexVector n)) ∞
    (realTransportBundle M)
  infer_instance

set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
/-- The genuine connection coefficients as a smooth bilinear-map-valued
function in a base chart. -/
theorem chartChristoffelBilin_contDiffOn (g : SmoothMetric M) (x : M.Carrier) :
    ContDiffOn ℝ ∞ (chartChristoffelBilin g.form x) (chartTarget x) := by
  apply contDiffOn_clm_apply.mpr
  intro u
  apply contDiffOn_clm_apply.mpr
  intro v
  simp only [chartChristoffelBilin_apply]
  apply ContDiffOn.sum
  intro c _
  apply ContDiffOn.smul_const
  apply ContDiffOn.sum
  intro a _
  apply ContDiffOn.sum
  intro b _
  exact ((christoffel_contDiffOn g x c a b).mul contDiffOn_const).mul contDiffOn_const

/-- The actual local geodesic and parallel-vector equations in a common
base chart, with two genuine tangent vectors. -/
def chartParallelTransportField (h : HermitianField M) (x : M.Carrier)
    (q : ComplexVector n × (ComplexVector n × ComplexVector n)) :
    ComplexVector n × (ComplexVector n × ComplexVector n) :=
  (q.2.1, (-chartChristoffelBilin h x q.1 q.2.1 q.2.1,
    -chartChristoffelBilin h x q.1 q.2.1 q.2.2))

def realTransportChartChange (a b : M.Carrier)
    (q : ComplexVector n × (ComplexVector n × ComplexVector n)) :
    ComplexVector n × (ComplexVector n × ComplexVector n) :=
  (realChartChange a b q.1, (fderiv ℝ (realChartChange a b) q.1 q.2.1,
    fderiv ℝ (realChartChange a b) q.1 q.2.2))

theorem chartParallelTransportField_contDiffOn (g : SmoothMetric M) (x : M.Carrier) :
    ContDiffOn ℝ ∞ (chartParallelTransportField g.form x)
      (chartTarget x ×ˢ Set.univ) := by
  have hΓ : ContDiffOn ℝ ∞
      (fun q : ComplexVector n × (ComplexVector n × ComplexVector n) =>
        chartChristoffelBilin g.form x q.1) (chartTarget x ×ˢ Set.univ) :=
    (chartChristoffelBilin_contDiffOn g x).comp contDiffOn_fst (fun _ hq => hq.1)
  have hv : ContDiffOn ℝ ∞
      (fun q : ComplexVector n × (ComplexVector n × ComplexVector n) => q.2.1)
      (chartTarget x ×ˢ Set.univ) := contDiffOn_snd.fst
  have hw : ContDiffOn ℝ ∞
      (fun q : ComplexVector n × (ComplexVector n × ComplexVector n) => q.2.2)
      (chartTarget x ×ˢ Set.univ) := contDiffOn_snd.snd
  exact hv.prodMk (((hΓ.clm_apply hv).clm_apply hv).neg.prodMk
    ((hΓ.clm_apply hv).clm_apply hw).neg)

theorem realTransportChartChange_contDiffAt (a b : M.Carrier)
    (q : ComplexVector n × (ComplexVector n × ComplexVector n))
    (hq : q.1 ∈ chartTarget a)
    (hy : chartInv a q.1 ∈ (extChartAt (ComplexModel n) b).source) :
    ContDiffAt ℝ ∞ (realTransportChartChange a b) q := by
  have hψ := realChartChange_contDiffAt a b hq hy
  have hD : ContDiffAt ℝ ∞ (fderiv ℝ (realChartChange a b)) q.1 := hψ.fderiv_right (by simp)
  have hbase := hψ.comp q contDiffAt_fst
  have hcoef := hD.comp q contDiffAt_fst
  exact hbase.prodMk ((hcoef.clm_apply contDiffAt_snd.fst).prodMk
    (hcoef.clm_apply contDiffAt_snd.snd))

/-- The two-vector field transforms by the actual tangent derivative.
This uses the genuine Levi--Civita Christoffel transformation law. -/
theorem realTransportChartChange_fderiv_field (g : SmoothMetric M) (a b : M.Carrier)
    (q : ComplexVector n × (ComplexVector n × ComplexVector n))
    (hq : q.1 ∈ chartTarget a)
    (hy : chartInv a q.1 ∈ (extChartAt (ComplexModel n) b).source) :
    fderiv ℝ (realTransportChartChange a b) q (chartParallelTransportField g.form a q) =
      chartParallelTransportField g.form b (realTransportChartChange a b q) := by
  have hψ := realChartChange_contDiffAt a b hq hy
  have hD : ContDiffAt ℝ ∞ (fderiv ℝ (realChartChange a b)) q.1 := hψ.fderiv_right (by simp)
  have hF := (hψ.differentiableAt (by simp)).hasFDerivAt.comp q (hasFDerivAt_fst (p := q))
  have hcoef := (hD.differentiableAt (by simp)).hasFDerivAt.comp q
    (hasFDerivAt_fst (p := q))
  have hV := hcoef.clm_apply (hasFDerivAt_snd (p := q)).fst
  have hW := hcoef.clm_apply (hasFDerivAt_snd (p := q)).snd
  have hJet := hF.prodMk (hV.prodMk hW)
  change fderiv ℝ (fun p : ComplexVector n × (ComplexVector n × ComplexVector n) =>
    ((realChartChange a b ∘ Prod.fst) p,
      (((fderiv ℝ (realChartChange a b) ∘ Prod.fst) p) p.2.1,
        ((fderiv ℝ (realChartChange a b) ∘ Prod.fst) p) p.2.2))) q
      (chartParallelTransportField g.form a q) = _
  rw [hJet.fderiv]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · change fderiv ℝ (realChartChange a b) q.1
        (-chartChristoffelBilin g.form a q.1 q.2.1 q.2.1) +
        fderiv ℝ (fderiv ℝ (realChartChange a b)) q.1 q.2.1 q.2.1 = _
      rw [map_neg, chartChristoffelBilin_change g a b hq hy q.2.1 q.2.1]
      dsimp only [chartParallelTransportField, realTransportChartChange]
      abel
    · change fderiv ℝ (realChartChange a b) q.1
        (-chartChristoffelBilin g.form a q.1 q.2.1 q.2.2) +
        fderiv ℝ (fderiv ℝ (realChartChange a b)) q.1 q.2.1 q.2.2 = _
      rw [map_neg, chartChristoffelBilin_change g a b hq hy q.2.1 q.2.2]
      dsimp only [chartParallelTransportField, realTransportChartChange]
      abel

def realTransportChart (x : M.Carrier) (q : realTransportBundle M) :
    ComplexVector n × (ComplexVector n × ComplexVector n) :=
  (chartPt x q.proj, (realTangentCoords x q.proj q.2.1,
    realTangentCoords x q.proj q.2.2))

def realTransportPoint (x : M.Carrier)
    (q : ComplexVector n × (ComplexVector n × ComplexVector n)) : realTransportBundle M :=
  ⟨chartInv x q.1, (realFrameCLM x (chartInv x q.1) q.2.1,
    realFrameCLM x (chartInv x q.1) q.2.2)⟩

set_option backward.isDefEq.respectTransparency false in
theorem realTransportChart_source (p q : realTransportBundle M) :
    letI := manifold_realSmooth M
    q ∈ (extChartAt (realTransportModel n) p).source ↔
      q.proj ∈ (chartAt (ComplexVector n) p.proj).source := by
  letI := manifold_realSmooth M
  let e₀ := trivializationAt (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n)) p.proj
  let e := e₀.prod e₀
  change q ∈ (extChartAt (𝓘(ℝ, ComplexVector n).prod
    𝓘(ℝ, ComplexVector n × ComplexVector n)) p).source ↔ _
  rw [FiberBundle.extChartAt]
  change (q ∈ e.source ∧
    ((e q).1 ∈ (extChartAt 𝓘(ℝ, ComplexVector n) p.proj).source ∧
      (e q).2 ∈ (Set.univ : Set (ComplexVector n × ComplexVector n)))) ↔ _
  constructor
  · intro hq
    exact (e.mem_source.mp hq.1).1
  · intro hq
    have hb : q.proj ∈ e.baseSet := ⟨hq, hq⟩
    have hqs := e.mem_source.mpr hb
    refine ⟨hqs, ?_, Set.mem_univ _⟩
    rw [e.coe_fst hqs]
    simpa only [extChartAt_source] using hq

set_option backward.isDefEq.respectTransparency false in
theorem realTransportChart_eq_extChartAt (p q : realTransportBundle M)
    (hq : q.proj ∈ (chartAt (ComplexVector n) p.proj).source) :
    letI := manifold_realSmooth M
    extChartAt (realTransportModel n) p q = realTransportChart p.proj q := by
  letI := manifold_realSmooth M
  let e₀ := trivializationAt (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n)) p.proj
  let e := e₀.prod e₀
  have hb : q.proj ∈ e₀.baseSet := hq
  have hqs : q ∈ e.source := e.mem_source.mpr ⟨hb, hb⟩
  change extChartAt (𝓘(ℝ, ComplexVector n).prod
    𝓘(ℝ, ComplexVector n × ComplexVector n)) p q = _
  rw [FiberBundle.extChartAt]
  change (chartPt p.proj (e q).1, (e q).2) = _
  rw [e.coe_fst hqs]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · exact (e₀.continuousLinearMapAt_apply_of_mem (R := ℝ) hb q.2.1).symm
    · exact (e₀.continuousLinearMapAt_apply_of_mem (R := ℝ) hb q.2.2).symm

theorem realTransportChart_realTransportPoint (x : M.Carrier)
    (q : ComplexVector n × (ComplexVector n × ComplexVector n))
    (hq : q.1 ∈ chartTarget x) : realTransportChart x (realTransportPoint x q) = q := by
  have hs : chartInv x q.1 ∈ (chartAt (ComplexVector n) x).source := by
    simpa only [extChartAt_source, chartInv] using (extChartAt (ComplexModel n) x).map_target hq
  apply Prod.ext
  · exact (extChartAt (ComplexModel n) x).right_inv hq
  · apply Prod.ext
    · exact realTangentCoords_realFrameCLM x (chartInv x q.1) hs q.2.1
    · exact realTangentCoords_realFrameCLM x (chartInv x q.1) hs q.2.2

theorem realTransportPoint_realTransportChart (x : M.Carrier) (q : realTransportBundle M)
    (hq : q.proj ∈ (chartAt (ComplexVector n) x).source) :
    realTransportPoint x (realTransportChart x q) = q := by
  have hp : chartInv x (chartPt x q.proj) = q.proj :=
    (extChartAt (ComplexModel n) x).left_inv (by simpa only [extChartAt_source] using hq)
  apply Bundle.TotalSpace.ext hp
  simp only [realTransportPoint, realTransportChart]
  rw [hp]
  exact heq_of_eq (Prod.ext (realFrameCLM_realTangentCoords x q.proj hq q.2.1)
    (realFrameCLM_realTangentCoords x q.proj hq q.2.2))

theorem realTransportPoint_eq_extChartAt_symm (p : realTransportBundle M)
    (q : ComplexVector n × (ComplexVector n × ComplexVector n))
    (hq : q.1 ∈ chartTarget p.proj) :
    letI := manifold_realSmooth M
    (extChartAt (realTransportModel n) p).symm q = realTransportPoint p.proj q := by
  letI := manifold_realSmooth M
  have hs : chartInv p.proj q.1 ∈ (chartAt (ComplexVector n) p.proj).source := by
    simpa only [extChartAt_source, chartInv] using (extChartAt (ComplexModel n) p.proj).map_target hq
  have hps : realTransportPoint p.proj q ∈ (extChartAt (realTransportModel n) p).source :=
    (realTransportChart_source p (realTransportPoint p.proj q)).mpr hs
  have hcode : extChartAt (realTransportModel n) p (realTransportPoint p.proj q) = q :=
    (realTransportChart_eq_extChartAt p (realTransportPoint p.proj q) hs).trans
      (realTransportChart_realTransportPoint p.proj q hq)
  have he := (extChartAt (realTransportModel n) p).left_inv hps
  rw [hcode] at he
  exact he

theorem realTransportChart_target (p : realTransportBundle M)
    (q : ComplexVector n × (ComplexVector n × ComplexVector n)) :
    letI := manifold_realSmooth M
    q ∈ (extChartAt (realTransportModel n) p).target ↔ q.1 ∈ chartTarget p.proj := by
  letI := manifold_realSmooth M
  change q ∈ (extChartAt (𝓘(ℝ, ComplexVector n).prod
    𝓘(ℝ, ComplexVector n × ComplexVector n)) p).target ↔ _
  rw [FiberBundle.extChartAt_target]
  constructor
  · intro hq
    exact hq.1.1
  · intro hq
    have hs : chartInv p.proj q.1 ∈ (chartAt (ComplexVector n) p.proj).source := by
      simpa only [extChartAt_source, chartInv] using (extChartAt (ComplexModel n) p.proj).map_target hq
    exact ⟨⟨hq, hs, hs⟩, Set.mem_univ _⟩

theorem realTransportChart_change (pA pB : realTransportBundle M)
    (q : ComplexVector n × (ComplexVector n × ComplexVector n))
    (hq : q.1 ∈ chartTarget pA.proj)
    (hB : chartInv pA.proj q.1 ∈ (extChartAt (ComplexModel n) pB.proj).source) :
    letI := manifold_realSmooth M
    extChartAt (realTransportModel n) pB ((extChartAt (realTransportModel n) pA).symm q) =
      realTransportChartChange pA.proj pB.proj q := by
  letI := manifold_realSmooth M
  have hAr : chartInv pA.proj q.1 ∈ (chartAt (ComplexVector n) pA.proj).source := by
    simpa only [extChartAt_source, chartInv] using (extChartAt (ComplexModel n) pA.proj).map_target hq
  have hBr : chartInv pA.proj q.1 ∈ (chartAt (ComplexVector n) pB.proj).source := by
    simpa only [extChartAt_source] using hB
  rw [realTransportPoint_eq_extChartAt_symm pA q hq,
    realTransportChart_eq_extChartAt pB (realTransportPoint pA.proj q) hBr]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · change realTangentCoords pB.proj (chartInv pA.proj q.1)
        (realFrameCLM pA.proj (chartInv pA.proj q.1) q.2.1) = _
      rw [realFrameCLM_apply pA.proj (chartInv pA.proj q.1) hAr]
      exact (realChartChange_fderiv pA.proj pB.proj hq hB q.2.1).symm
    · change realTangentCoords pB.proj (chartInv pA.proj q.1)
        (realFrameCLM pA.proj (chartInv pA.proj q.1) q.2.2) = _
      rw [realFrameCLM_apply pA.proj (chartInv pA.proj q.1) hAr]
      exact (realChartChange_fderiv pA.proj pB.proj hq hB q.2.2).symm

theorem realTransportModel_boundaryless (n : ℕ) :
    ModelWithCorners.Boundaryless (realTransportModel n) := by
  change ModelWithCorners.Boundaryless
    (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n × ComplexVector n))
  infer_instance

theorem realTransportChart_change_eventually
    (pA pB : realTransportBundle M)
    (q : ComplexVector n × (ComplexVector n × ComplexVector n)) (hq : q.1 ∈ chartTarget pA.proj)
    (hB : chartInv pA.proj q.1 ∈ (extChartAt (ComplexModel n) pB.proj).source) :
    letI := manifold_realSmooth M
    (extChartAt (realTransportModel n) pB ∘ (extChartAt (realTransportModel n) pA).symm)
      =ᶠ[𝓝 q] realTransportChartChange pA.proj pB.proj := by
  letI := manifold_realSmooth M
  letI := realTransportModel_boundaryless n
  have hqA : q ∈ (extChartAt (realTransportModel n) pA).target :=
    (realTransportChart_target pA q).mpr hq
  have hpB : (extChartAt (realTransportModel n) pA).symm q ∈
      (extChartAt (realTransportModel n) pB).source := by
    rw [realTransportPoint_eq_extChartAt_symm pA q hq, realTransportChart_source]
    simpa only [realTransportPoint, extChartAt_source] using hB
  have hnB : (extChartAt (realTransportModel n) pA).symm ⁻¹'
      (extChartAt (realTransportModel n) pB).source ∈ 𝓝 q :=
    (continuousAt_extChartAt_symm'' hqA).preimage_mem_nhds
      ((isOpen_extChartAt_source (I := realTransportModel n) pB).mem_nhds hpB)
  filter_upwards [(isOpen_extChartAt_target (I := realTransportModel n) pA).mem_nhds hqA,
    hnB] with r hrA hrB
  have hr : r.1 ∈ chartTarget pA.proj := (realTransportChart_target pA r).mp hrA
  have hr' : chartInv pA.proj r.1 ∈ (extChartAt (ComplexModel n) pB.proj).source := by
    change (extChartAt (realTransportModel n) pA).symm r ∈
      (extChartAt (realTransportModel n) pB).source at hrB
    rw [realTransportPoint_eq_extChartAt_symm pA r hr, realTransportChart_source] at hrB
    simpa only [realTransportPoint, extChartAt_source] using hrB
  exact realTransportChart_change pA pB r hr hr'

theorem realTransportChart_change_fderiv_spray (g : SmoothMetric M)
    (pA pB : realTransportBundle M)
    (q : ComplexVector n × (ComplexVector n × ComplexVector n)) (hq : q.1 ∈ chartTarget pA.proj)
    (hB : chartInv pA.proj q.1 ∈ (extChartAt (ComplexModel n) pB.proj).source) :
    letI := manifold_realSmooth M
    fderiv ℝ (extChartAt (realTransportModel n) pB ∘ (extChartAt (realTransportModel n) pA).symm) q
      (chartParallelTransportField g.form pA.proj q) =
        chartParallelTransportField g.form pB.proj (realTransportChartChange pA.proj pB.proj q) := by
  letI := manifold_realSmooth M
  rw [(realTransportChart_change_eventually pA pB q hq hB).fderiv_eq]
  exact realTransportChartChange_fderiv_field g pA.proj pB.proj q hq hB

/-- The genuine geodesic and parallel-vector equations as a smooth vector field on the Whitney sum. -/
def realParallelTransportSpray (g : SmoothMetric M)
    (q : realTransportBundle M) :
    letI := manifold_realSmooth M
    TangentSpace (realTransportModel n) q := by
  letI := manifold_realSmooth M
  exact chartParallelTransportField g.form q.proj (realTransportChart q.proj q)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem realParallelTransportSpray_in_phaseChart (g : SmoothMetric M)
    (p q : realTransportBundle M)
    (hq : q.proj ∈ (chartAt (ComplexVector n) p.proj).source) :
    letI := manifold_realSmooth M
    letI := manifold_realTransport M
    (trivializationAt (ComplexVector n × (ComplexVector n × ComplexVector n))
      (TangentSpace (realTransportModel n)) p
        (⟨q, realParallelTransportSpray g q⟩ : TangentBundle (realTransportModel n)
          (realTransportBundle M))).2 =
      chartParallelTransportField g.form p.proj (realTransportChart p.proj q) := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  letI := realTransportModel_boundaryless n
  have hself : q.proj ∈ (chartAt (ComplexVector n) q.proj).source := mem_chart_source _ _
  have hqa : (realTransportChart q.proj q).1 ∈ chartTarget q.proj := mem_extChartAt_target _
  have hqb : chartInv q.proj (realTransportChart q.proj q).1 ∈
      (extChartAt (ComplexModel n) p.proj).source := by
    change (extChartAt (ComplexModel n) q.proj).symm
      (extChartAt (ComplexModel n) q.proj q.proj) ∈ _
    rw [(extChartAt (ComplexModel n) q.proj).left_inv (mem_extChartAt_source _)]
    simpa only [extChartAt_source] using hq
  have hchange := realTransportChart_change q p (realTransportChart q.proj q) hqa hqb
  rw [← realTransportChart_eq_extChartAt q q hself,
    (extChartAt (realTransportModel n) q).left_inv (mem_extChartAt_source _),
    realTransportChart_eq_extChartAt p q hq] at hchange
  rw [realTransportChart_eq_extChartAt q q hself] at hchange
  change fderivWithin ℝ
      (extChartAt (realTransportModel n) p ∘ (extChartAt (realTransportModel n) q).symm)
      (Set.range (realTransportModel n)) (extChartAt (realTransportModel n) q q)
      (realParallelTransportSpray g q) = _
  rw [ModelWithCorners.range_eq_univ, fderivWithin_univ,
    realTransportChart_eq_extChartAt q q hself]
  change fderiv ℝ
      (extChartAt (realTransportModel n) p ∘ (extChartAt (realTransportModel n) q).symm)
      (realTransportChart q.proj q) (chartParallelTransportField g.form q.proj (realTransportChart q.proj q)) = _
  rw [realTransportChart_change_fderiv_spray g q p _ hqa hqb, ← hchange]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem realParallelTransportSpray_contMDiff (g : SmoothMetric M) :
    letI := manifold_realSmooth M
    letI := manifold_realTransport M
    ContMDiff (realTransportModel n)
      ((realTransportModel n).prod 𝓘(ℝ, ComplexVector n × (ComplexVector n × ComplexVector n))) ∞
      (fun q : realTransportBundle M =>
        (⟨q, realParallelTransportSpray g q⟩ : TangentBundle (realTransportModel n)
          (realTransportBundle M))) := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  intro p
  apply (Bundle.contMDiffAt_section (IB := realTransportModel n)
    (s := realParallelTransportSpray g) p).mpr
  have hs := (chartParallelTransportField_contDiffOn g p.proj).contDiffAt
    (((isOpen_extChartAt_target (I := ComplexModel n) p.proj).prod isOpen_univ).mem_nhds
      (show realTransportChart p.proj p ∈ chartTarget p.proj ×ˢ Set.univ from
        ⟨mem_extChartAt_target _, Set.mem_univ _⟩))
  have hp : ContMDiffAt (realTransportModel n) 𝓘(ℝ, ComplexVector n × (ComplexVector n × ComplexVector n)) ∞
      (extChartAt (realTransportModel n) p) p :=
    contMDiffAt_extChartAt
  rw [← realTransportChart_eq_extChartAt p p (mem_chart_source _ _)] at hs
  have hsp := hs.contMDiffAt.comp p hp
  apply hsp.congr_of_eventuallyEq
  filter_upwards [extChartAt_source_mem_nhds (I := realTransportModel n) p] with q hq
  have hb := (realTransportChart_source p q).mp hq
  rw [realParallelTransportSpray_in_phaseChart g p q hb]
  exact congrArg (chartParallelTransportField g.form p.proj)
    (realTransportChart_eq_extChartAt p q hb).symm

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem tangentCoordChange_realParallelTransportSpray (g : SmoothMetric M)
    (p q : realTransportBundle M)
    : letI := manifold_realSmooth M
    letI := manifold_realTransport M
    ∀ (hq : q ∈ (extChartAt (realTransportModel n) p).source),
    tangentCoordChange (realTransportModel n) q p q (realParallelTransportSpray g q) =
      chartParallelTransportField g.form p.proj (extChartAt (realTransportModel n) p q) := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  intro hq
  have hbase := (realTransportChart_source p q).mp hq
  have h := realParallelTransportSpray_in_phaseChart g p q hbase
  change tangentCoordChange (realTransportModel n) q p q (realParallelTransportSpray g q) = _ at h
  rw [← realTransportChart_eq_extChartAt p q hbase] at h
  exact h


def realTransportVelocity (q : realTransportBundle M) :
    TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier := (realTransportDiag q).1

def realTransportVector (q : realTransportBundle M) :
    TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier := (realTransportDiag q).2

theorem realTransportDiag_injective : Function.Injective (realTransportDiag (M := M)) := by
  intro p q h
  rcases p with ⟨x, v, w⟩
  rcases q with ⟨y, u, z⟩
  have h₁ : (⟨x, v⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) = ⟨y, u⟩ :=
    congrArg Prod.fst h
  cases h₁
  have h₂ : (⟨x, w⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) = ⟨x, z⟩ :=
    congrArg Prod.snd h
  cases h₂
  rfl

theorem realTransport_t2Space (M : ComplexManifold n) :
    letI := manifold_realSmooth M
    T2Space (realTransportBundle M) := by
  letI := manifold_realSmooth M
  letI := realPhase_t2Space M
  exact T2Space.of_injective_continuous realTransportDiag_injective
    (FiberBundle.Prod.isInducing_diag (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n))
      (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n))).continuous

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
theorem realTransportVelocity_contMDiff :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI := manifold_realTransport M
    ContMDiff (realTransportModel n) (realPhaseModel n) ∞
      (realTransportVelocity (M := M)) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := manifold_realTransport M
  intro q
  apply Bundle.contMDiffAt_totalSpace.mpr
  have hid : ContMDiffAt (realTransportModel n) (realTransportModel n) ∞
      (id : realTransportBundle M → realTransportBundle M) q := contMDiffAt_id
  have hp := Bundle.contMDiffAt_totalSpace.mp hid
  exact ⟨hp.1, (ContinuousLinearMap.fst ℝ (ComplexVector n)
    (ComplexVector n)).contMDiff.contMDiffAt.comp q hp.2⟩

def realTransportVelocityCLM (n : ℕ) :
    (ComplexVector n × (ComplexVector n × ComplexVector n)) →L[ℝ]
      (ComplexVector n × ComplexVector n) :=
  (ContinuousLinearMap.fst ℝ (ComplexVector n) (ComplexVector n × ComplexVector n)).prod
    ((ContinuousLinearMap.fst ℝ (ComplexVector n) (ComplexVector n)).comp
      (ContinuousLinearMap.snd ℝ (ComplexVector n) (ComplexVector n × ComplexVector n)))

set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
theorem mfderiv_realTransportVelocity (q : realTransportBundle M) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI := manifold_realTransport M
    mfderiv (realTransportModel n) (realPhaseModel n) realTransportVelocity q =
      realTransportVelocityCLM n := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := manifold_realTransport M
  letI := realTransportModel_boundaryless n
  have hf := (realTransportVelocity_contMDiff (M := M) q).mdifferentiableAt (by simp)
  have heq : writtenInExtChartAt (realTransportModel n) (realPhaseModel n) q
      realTransportVelocity =ᶠ[𝓝 (extChartAt (realTransportModel n) q q)]
      realTransportVelocityCLM n := by
    filter_upwards [(isOpen_extChartAt_target (I := realTransportModel n) q).mem_nhds
      (mem_extChartAt_target q)] with r hr
    have hz := (realTransportChart_target q r).mp hr
    have hs : chartInv q.proj r.1 ∈ (chartAt (ComplexVector n) q.proj).source := by
      simpa only [extChartAt_source, chartInv] using
        (extChartAt (ComplexModel n) q.proj).map_target hz
    change extChartAt (realPhaseModel n) (realTransportVelocity q)
      (realTransportVelocity ((extChartAt (realTransportModel n) q).symm r)) = _
    rw [realTransportPoint_eq_extChartAt_symm q r hz]
    rw [realPhaseChart_eq_extChartAt (realTransportVelocity q)
      (realTransportVelocity (realTransportPoint q.proj r)) hs]
    exact realPhaseChart_realPhasePoint q.proj (r.1, r.2.1) hz
  rw [hf.mfderiv_abuse, ModelWithCorners.range_eq_univ, fderivWithin_univ,
    heq.fderiv_eq, (realTransportVelocityCLM n).hasFDerivAt.fderiv]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
theorem mfderiv_realTransportVelocity_spray (g : SmoothMetric M) (q : realTransportBundle M) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI := manifold_realTransport M
    mfderiv (realTransportModel n) (realPhaseModel n) realTransportVelocity q
      (realParallelTransportSpray g q) = realGeodesicSpray g (realTransportVelocity q) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := manifold_realTransport M
  rw [mfderiv_realTransportVelocity]
  change (_, -chartChristoffelBilin g.form q.proj (chartPt q.proj q.proj)
      (realTangentCoords q.proj q.proj q.2.1) (realTangentCoords q.proj q.proj q.2.1)) =
    (_, chartGeodesicAcceleration g.form q.proj (chartPt q.proj q.proj)
      (realTangentCoords q.proj q.proj q.2.1))
  rw [chartGeodesicAcceleration_eq]
  rfl

set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
theorem realTransportVelocity_isMIntegralCurveOn (g : SmoothMetric M)
    (γ : ℝ → realTransportBundle M) {s : Set ℝ} :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI := manifold_realTransport M
    IsMIntegralCurveOn γ (realParallelTransportSpray g) s →
      IsMIntegralCurveOn (realTransportVelocity ∘ γ) (realGeodesicSpray g) s := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := manifold_realTransport M
  intro hγ t ht
  have hf := (realTransportVelocity_contMDiff (M := M) (γ t)).mdifferentiableAt (by simp)
  have hc := hf.hasMFDerivAt.comp_hasMFDerivWithinAt t (hγ t ht)
  convert hc using 1
  apply ContinuousLinearMap.ext
  intro a
  change ((1 : ℝ →L[ℝ] ℝ).smulRight (realGeodesicSpray g (realTransportVelocity (γ t)))) a =
    (mfderiv (realTransportModel n) (realPhaseModel n) realTransportVelocity (γ t))
      (((1 : ℝ →L[ℝ] ℝ).smulRight (realParallelTransportSpray g (γ t))) a)
  rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smulRight_apply,
    map_smul, mfderiv_realTransportVelocity_spray]

set_option synthInstance.maxHeartbeats 200000 in
/-- Metric compatibility of the actual Levi--Civita connection conserves
the pairing of two coordinate-parallel vector fields. -/
theorem realMetricInChart_parallelPair_hasDerivAt (g : SmoothMetric M) (x : M.Carrier)
    {z a b : ℝ → ComplexVector n} {t : ℝ} {u : ComplexVector n}
    (hz : z t ∈ chartTarget x) (hzu : HasDerivAt z u t)
    (ha : HasDerivAt a (-chartChristoffelBilin g.form x (z t) u (a t)) t)
    (hb : HasDerivAt b (-chartChristoffelBilin g.form x (z t) u (b t)) t) :
    HasDerivAt (fun s => realMetricInChart g.form x (z s) (a s) (b s)) 0 t := by
  have hB := ((realMetricInChart_smooth g x).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hDB : HasDerivAt (fun s => realMetricInChart g.form x (z s))
      (fderiv ℝ (realMetricInChart g.form x) (z t) u) t :=
    hB.hasFDerivAt.comp_hasDerivAt t hzu
  have hpair := (hDB.clm_apply ha).clm_apply hb
  convert hpair using 1
  simp only [ContinuousLinearMap.add_apply, map_neg, ContinuousLinearMap.neg_apply]
  rw [realMetricInChart_connection_compatibility g x (z t) hz u (a t) (b t)]
  ring

def chartTransportedEnergy (h : HermitianField M) (x : M.Carrier)
    (q : ComplexVector n × (ComplexVector n × ComplexVector n)) : ℝ :=
  realMetricInChart h x q.1 q.2.2 q.2.2

theorem chartTransportedEnergy_hasDerivAt (g : SmoothMetric M) (x : M.Carrier)
    (η : ℝ → ComplexVector n × (ComplexVector n × ComplexVector n)) {t : ℝ}
    (hz : (η t).1 ∈ chartTarget x)
    (hη : HasDerivAt η (chartParallelTransportField g.form x (η t)) t) :
    HasDerivAt (fun s => chartTransportedEnergy g.form x (η s)) 0 t := by
  have hzu : HasDerivAt (fun s => (η s).1) (η t).2.1 t :=
    (ContinuousLinearMap.fst ℝ (ComplexVector n)
      (ComplexVector n × ComplexVector n)).hasFDerivAt.comp_hasDerivAt t hη
  let W := (ContinuousLinearMap.snd ℝ (ComplexVector n) (ComplexVector n)).comp
    (ContinuousLinearMap.snd ℝ (ComplexVector n) (ComplexVector n × ComplexVector n))
  have hw : HasDerivAt (fun s => (η s).2.2)
      (-chartChristoffelBilin g.form x (η t).1 (η t).2.1 (η t).2.2) t :=
    W.hasFDerivAt.comp_hasDerivAt t hη
  exact realMetricInChart_parallelPair_hasDerivAt g x hz hzu hw hw

def realTransportedEnergy (h : HermitianField M) (q : realTransportBundle M) : ℝ :=
  realTangentEnergy h (realTransportVector q)

theorem realTransportedEnergy_in_chart (h : HermitianField M) (x : M.Carrier)
    (q : realTransportBundle M) (hq : q.proj ∈ (chartAt (ComplexVector n) x).source) :
    realTransportedEnergy h q = chartTransportedEnergy h x (realTransportChart x q) :=
  realTangentEnergy_in_phaseChart h x (realTransportVector q) hq

set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem realTransportedEnergy_hasDerivAt (g : SmoothMetric M)
    (γ : ℝ → realTransportBundle M) {t₀ : ℝ} :
    letI := manifold_realSmooth M
    letI := manifold_realTransport M
    IsMIntegralCurveAt γ (realParallelTransportSpray g) t₀ →
      HasDerivAt (fun t => realTransportedEnergy g.form (γ t)) 0 t₀ := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  intro hγ
  let p := γ t₀
  let η := extChartAt (realTransportModel n) p ∘ γ
  have hη := hγ.eventually_hasDerivAt.self_of_nhds
  rw [tangentCoordChange_realParallelTransportSpray g p p (mem_extChartAt_source p)] at hη
  have hz : (η t₀).1 ∈ chartTarget p.proj :=
    (realTransportChart_target p (η t₀)).mp (mem_extChartAt_target p)
  have hE := chartTransportedEnergy_hasDerivAt g p.proj η hz hη
  apply hE.congr_of_eventuallyEq
  filter_upwards [hγ.continuousAt.preimage_mem_nhds
    (extChartAt_source_mem_nhds (I := realTransportModel n) p)] with t ht
  have hbase := (realTransportChart_source p (γ t)).mp ht
  rw [realTransportedEnergy_in_chart g.form p.proj (γ t) hbase]
  exact congrArg (chartTransportedEnergy g.form p.proj)
    (realTransportChart_eq_extChartAt p (γ t) hbase).symm

set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem realTransportedEnergy_constant (g : SmoothMetric M)
    (γ : ℝ → realTransportBundle M) {a b s t : ℝ} :
    letI := manifold_realSmooth M
    letI := manifold_realTransport M
    IsMIntegralCurveOn γ (realParallelTransportSpray g) (Set.Ioo a b) →
      s ∈ Set.Ioo a b → t ∈ Set.Ioo a b →
        realTransportedEnergy g.form (γ s) = realTransportedEnergy g.form (γ t) := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  intro hγ hs ht
  apply isOpen_Ioo.is_const_of_deriv_eq_zero
    (f := fun r => realTransportedEnergy g.form (γ r)) (convex_Ioo a b).isPreconnected
  · intro r hr
    exact (realTransportedEnergy_hasDerivAt g γ
      (hγ.isMIntegralCurveAt (Ioo_mem_nhds hr.1 hr.2))).differentiableAt.differentiableWithinAt
  · intro r hr
    exact (realTransportedEnergy_hasDerivAt g γ
      (hγ.isMIntegralCurveAt (Ioo_mem_nhds hr.1 hr.2))).deriv
  · exact hs
  · exact ht

set_option maxHeartbeats 1400000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- Genuine complete geodesic and parallel-vector trajectories, with no
auxiliary completeness assumption on the Whitney-sum space. -/
theorem exists_global_realParallelTransport (g : SmoothMetric M) (p : realTransportBundle M) :
    letI := manifold_realSmooth M
    letI := manifold_realTransport M
    ∃ γ : ℝ → realTransportBundle M, γ 0 = p ∧
      IsMIntegralCurve γ (realParallelTransportSpray g) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := manifold_realTransport M
  letI := realTransportModel_boundaryless n
  letI := realTransport_t2Space M
  have hv := (realParallelTransportSpray_contMDiff g).of_le
    (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)
  apply exists_global_integral_curve_of_compact_trapping hv p
  intro T hT
  let A := realTangentEnergy g.form (realTransportVelocity p)
  let B := realTransportedEnergy g.form p
  let c := Real.sqrt A
  let Kbase : Set M.Carrier := {x | inducedDistance g.form p.proj x ≤ c * T}
  have hKbase : IsCompact Kbase := isCompact_inducedDistance_sublevel g p.proj (c * T)
  refine ⟨{q : realTransportBundle M | q.proj ∈ Kbase ∧
      realTangentEnergy g.form (realTransportDiag q).1 ≤ A ∧
      realTangentEnergy g.form (realTransportDiag q).2 ≤ B},
    isCompact_realTransportEnergy_sublevel g hKbase A B, ?_⟩
  intro a ha haT γ hγ0 hγ t ht
  have h0 : (0 : ℝ) ∈ Set.Ioo (-a) a := ⟨by linarith, ha⟩
  have hγv := realTransportVelocity_isMIntegralCurveOn g γ hγ
  have hEv := realGeodesicEnergy_constant g (realTransportVelocity ∘ γ) hγv ht h0
  have hEw := realTransportedEnergy_constant g γ hγ ht h0
  simp only [Function.comp_apply, hγ0] at hEv
  rw [hγ0] at hEw
  refine ⟨?_, hEv.le, hEw.le⟩
  have hγv0 : (realTransportVelocity ∘ γ) 0 = realTransportVelocity p := by
    rw [Function.comp_apply, hγ0]
  have hd := realGeodesic_distFrom_le g (realTransportVelocity ∘ γ)
    (realTransportVelocity p) ha hγv0 hγv ht
  exact hd.trans (mul_le_mul_of_nonneg_left
    ((abs_lt.mpr ht).le.trans haT) (Real.sqrt_nonneg A))

end Yau.LeafProofs.L12Aux
