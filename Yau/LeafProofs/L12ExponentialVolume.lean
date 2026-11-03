import Yau.LeafProofs.L12GaussLemma

/-! The genuine exponential differential, its physical Gram Jacobian,
and the resulting radial density comparison before singularities. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff Bundle ComplexOrder InnerProductSpace
namespace Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

/-- The actual differential of the actual exponential, with the canonical
source tangent identification written explicitly. -/
def realExponentialDifferential (g : SmoothMetric M) (x : M.Carrier)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) x) :
    TangentSpace 𝓘(ℝ, ComplexVector n) x →L[ℝ]
      TangentSpace 𝓘(ℝ, ComplexVector n) (realExponentialMap g x v) := by
  letI := manifold_realSmooth M
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI := underlyingRealTangentInnerProductSpace g.form x
  exact (mfderiv 𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) x) 𝓘(ℝ, ComplexVector n)
    (realExponentialMap g x) v).comp
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) v).symm.toContinuousLinearMap)

theorem realExponentialDifferential_eq_JacobiField (g : SmoothMetric M) (x : M.Carrier)
    (v w : TangentSpace 𝓘(ℝ, ComplexVector n) x) :
    realExponentialDifferential g x v w =
      realGeodesicJacobiField g (⟨x, v⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) w 1 := rfl

theorem realExponentialDifferential_coords (g : SmoothMetric M) (x y : M.Carrier)
    (v w : TangentSpace 𝓘(ℝ, ComplexVector n) x)
    (hy : realExponentialMap g x v ∈ (chartAt (ComplexVector n) y).source) :
    letI := manifold_realSmooth M
    letI := underlyingRealTangentNormedAddCommGroup g.form x
    letI := underlyingRealTangentInnerProductSpace g.form x
    realTangentCoords y (realExponentialMap g x v) (realExponentialDifferential g x v w) =
      fderiv ℝ (fun a => chartPt y (realExponentialMap g x a)) v w := by
  letI := manifold_realSmooth M
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI := underlyingRealTangentInnerProductSpace g.form x
  exact realTangentCoords_mfderiv (realExponentialMap g x) v y hy w
    ((realExponentialMap_contMDiff g x).mdifferentiableAt (by simp))

theorem realGeodesicJacobiField_in_chart (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) (t : ℝ) (x : M.Carrier)
    (hx : (realGeodesicFlow g p t).proj ∈ (chartAt (ComplexVector n) x).source) :
    letI := manifold_realSmooth M
    letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
    letI := underlyingRealTangentInnerProductSpace g.form p.proj
    realTangentCoords x (realGeodesicFlow g p t).proj (realGeodesicJacobiField g p w t) =
      fderiv ℝ (fun a => chartPt x (realVelocityBaseFlow g p.proj a t)) p.2 w := by
  letI := manifold_realSmooth M
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  exact realTangentCoords_mfderiv (fun a => realVelocityBaseFlow g p.proj a t) p.2 x hx w
    ((realVelocityBaseFlow_contMDiff g p.proj t p.2).mdifferentiableAt (by simp))

theorem realTangentPoint_eq_of_coords {x y z : M.Carrier}
    {u : TangentSpace 𝓘(ℝ, ComplexVector n) x} {v : TangentSpace 𝓘(ℝ, ComplexVector n) y}
    (hxy : x = y) (hx : x ∈ (chartAt (ComplexVector n) z).source)
    (hc : realTangentCoords z x u = realTangentCoords z y v) :
    (⟨x, u⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) = ⟨y, v⟩ := by
  subst y
  have huv := congrArg (realFrameCLM z x) hc
  rw [realFrameCLM_realTangentCoords z x hx, realFrameCLM_realTangentCoords z x hx] at huv
  exact congrArg (fun a => (⟨x, a⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)) huv

/-- The actual Jacobi differential at time t is t times the actual
exponential differential at the scaled initial vector, as genuine bundle points. -/
theorem realGeodesicJacobiField_eq_scaled_exponentialDifferential (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) (t : ℝ) :
    (⟨(realGeodesicFlow g p t).proj, realGeodesicJacobiField g p w t⟩ :
      TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) =
      ⟨realExponentialMap g p.proj (t • p.2), t • realExponentialDifferential g p.proj (t • p.2) w⟩ := by
  letI := manifold_realSmooth M
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  let y := (realGeodesicFlow g p t).proj
  have hbase : y = realExponentialMap g p.proj (t • p.2) :=
    (realExponentialMap_smul g p.proj p.2 t).symm
  have hsrc : realExponentialMap g p.proj (t • p.2) ∈ (chartAt (ComplexVector n) y).source := by
    rw [← hbase]
    exact mem_chart_source _ _
  let F : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj → ComplexVector n :=
    fun a => chartPt y (realExponentialMap g p.proj a)
  have hchart : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 1 (chartPt y)
      (realExponentialMap g p.proj (t • p.2)) :=
    contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hsrc)
  have hF : DifferentiableAt ℝ F (t • p.2) :=
    (hchart.comp _ ((realExponentialMap_contMDiff g p.proj).contMDiffAt)).contDiffAt.differentiableAt (by simp)
  let S : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj →L[ℝ]
      TangentSpace 𝓘(ℝ, ComplexVector n) p.proj := t • ContinuousLinearMap.id ℝ _
  have hs : S p.2 = t • p.2 := rfl
  have hcomp : HasFDerivAt (F ∘ S) ((fderiv ℝ F (t • p.2)).comp S) p.2 :=
    hs ▸ hF.hasFDerivAt.comp p.2 S.hasFDerivAt
  have heq : (fun a => chartPt y (realVelocityBaseFlow g p.proj a t)) = F ∘ S := by
    funext a
    rw [realVelocityBaseFlow, ← realExponentialMap_smul g p.proj a t]
    rfl
  apply realTangentPoint_eq_of_coords hbase (mem_chart_source _ _)
  rw [realGeodesicJacobiField_in_chart g p w t y (mem_chart_source _ _), map_smul,
    realExponentialDifferential_coords g p.proj y (t • p.2) w hsrc,
    heq, hcomp.fderiv, ContinuousLinearMap.comp_apply]
  change fderiv ℝ F (t • p.2) (t • w) = t • fderiv ℝ F (t • p.2) w
  exact map_smul _ t w

/-- Gram matrix of the genuine exponential differential in a physical
orthonormal initial basis. -/
def realExponentialGramMatrix (g : SmoothMetric M) (x : M.Carrier)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) x) : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ :=
  fun i j => (underlyingRealRiemannianMetric g.form).inner (realExponentialMap g x v)
    (realExponentialDifferential g x v (realInitialOrthonormalFrame g x i))
    (realExponentialDifferential g x v (realInitialOrthonormalFrame g x j))

def realJacobiGramMatrix (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ := fun i j =>
  (underlyingRealRiemannianMetric g.form).inner (realGeodesicFlow g p t).proj
    (realGeodesicJacobiField g p (realInitialOrthonormalFrame g p.proj i) t)
    (realGeodesicJacobiField g p (realInitialOrthonormalFrame g p.proj j) t)

theorem realJacobiGramMatrix_eq_matrix_mul (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) :
    realJacobiGramMatrix g p t =
      (realGeodesicJacobiMatrix g p t)ᵀ * realGeodesicJacobiMatrix g p t := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  ext i j
  change ⟪realGeodesicJacobiField g p (realInitialOrthonormalFrame g p.proj i) t,
    realGeodesicJacobiField g p (realInitialOrthonormalFrame g p.proj j) t⟫_ℝ =
      ∑ k, ⟪realGlobalParallelFrame g p t k,
        realGeodesicJacobiField g p (realInitialOrthonormalFrame g p.proj i) t⟫_ℝ *
        ⟪realGlobalParallelFrame g p t k,
          realGeodesicJacobiField g p (realInitialOrthonormalFrame g p.proj j) t⟫_ℝ
  rw [← (realGlobalParallelFrame g p t).sum_inner_mul_inner]
  apply Finset.sum_congr rfl
  intro k _
  rw [real_inner_comm (realGeodesicJacobiField g p (realInitialOrthonormalFrame g p.proj i) t)]

theorem realJacobiGramMatrix_eq_scaled_exponentialGram (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) :
    realJacobiGramMatrix g p t = (t ^ 2) • realExponentialGramMatrix g p.proj (t • p.2) := by
  ext i j
  have h := realMetric_pairing_of_totalSpace_eq g.form
    (realGeodesicJacobiField_eq_scaled_exponentialDifferential g p (realInitialOrthonormalFrame g p.proj i) t)
    (realGeodesicJacobiField_eq_scaled_exponentialDifferential g p (realInitialOrthonormalFrame g p.proj j) t)
  simpa only [realJacobiGramMatrix, realExponentialGramMatrix, Matrix.smul_apply,
    map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, pow_two, mul_assoc] using h

/-- Riemannian Jacobian density of the actual exponential, as the Gram
determinant of its genuine differential and the physical initial volume. -/
def realExponentialVolumeDensity (g : SmoothMetric M) (x : M.Carrier)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) x) : ℝ :=
  Real.sqrt (realExponentialGramMatrix g x v).det

theorem realExponentialVolumeDensity_nonneg (g : SmoothMetric M) (x : M.Carrier)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) x) : 0 ≤ realExponentialVolumeDensity g x v :=
  Real.sqrt_nonneg _

theorem realExponentialVolumeDensity_radial (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) {t : ℝ} (ht : 0 < t) :
    realExponentialVolumeDensity g p.proj (t • p.2) =
      |(realGeodesicJacobiMatrix g p t).det| / t ^ (2 * n) := by
  have hGram := (realJacobiGramMatrix_eq_matrix_mul g p t).symm.trans
    (realJacobiGramMatrix_eq_scaled_exponentialGram g p t)
  have hdet := congrArg Matrix.det hGram
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Fintype.card_fin] at hdet
  have hpow : (t ^ 2) ^ (2 * n) = (t ^ (2 * n)) ^ 2 := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 (2 * n)]
  rw [hpow, ← pow_two] at hdet
  have hs := congrArg Real.sqrt hdet
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg ht.le _)] at hs
  apply (eq_div_iff (pow_ne_zero _ ht.ne')).mpr
  simpa only [realExponentialVolumeDensity, mul_comm] using hs.symm

/-- The genuine exponential volume density decreases along each radial
ray up to any first singularity, under the project's actual Ricci condition. -/
theorem realExponentialVolumeDensity_radial_antitone (g : SmoothMetric M)
    (hK : IsKahler g) (hR : ∀ x, (ricci g.form x).PosSemidef)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (T : ℝ)
    (hdet : ∀ t ∈ Set.Ioo 0 T, 0 < (realGeodesicJacobiMatrix g p t).det) :
    AntitoneOn (fun t => realExponentialVolumeDensity g p.proj (t • p.2)) (Set.Ioo 0 T) := by
  intro s hs t ht hst
  dsimp only
  rw [realExponentialVolumeDensity_radial g p hs.1,
    realExponentialVolumeDensity_radial g p ht.1,
    abs_of_pos (hdet s hs), abs_of_pos (hdet t ht)]
  exact realGeodesicJacobiMatrix_det_ratio_antitone g hK hR p T hdet hs ht hst

theorem realExponentialVolumeDensity_le_one (g : SmoothMetric M)
    (hK : IsKahler g) (hR : ∀ x, (ricci g.form x).PosSemidef)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (T : ℝ)
    (hdet : ∀ t ∈ Set.Ioo 0 T, 0 < (realGeodesicJacobiMatrix g p t).det)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) :
    realExponentialVolumeDensity g p.proj (t • p.2) ≤ 1 := by
  rw [realExponentialVolumeDensity_radial g p ht.1, abs_of_pos (hdet t ht)]
  apply ge_of_tendsto (realGeodesicJacobiMatrix_normalized_det_initial_limit g p)
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht.1)] with s hs hst
  exact realGeodesicJacobiMatrix_det_ratio_antitone g hK hR p T hdet
    ⟨hs, hst.trans ht.2⟩ ht hst.le

end Yau.LeafProofs.L12Aux
