import Yau.LeafProofs.L23JetBernsteinLocal
import Yau.LeafProofs.L23BernsteinTimeBound
import Yau.LeafProofs.L23LocalDistanceSupportContinuity

/-! Compact buffered distance cutoffs meet every scalar localization condition. -/

noncomputable section
open Filter
open scoped Topology ContDiff
namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem continuous_cutoff_zero_on_boundary (S : Set M.Carrier)
    (η : M.Carrier → ℝ) (hη : Continuous η)
    (hsupp : ∀ y, η y≠0 → y∈S) (y : M.Carrier) (hy : y∉interior S) : η y=0 := by
  by_contra hne
  have hnear : ∀ᶠ z in 𝓝 y, η z≠0 := hη.continuousAt.eventually_ne hne
  apply hy
  apply mem_interior_iff_mem_nhds.mpr
  exact Filter.mem_of_superset hnear (fun z hz => hsupp z hz)

theorem local_flow_timeDistanceCutoff_zero_on_buffer_boundary
    (h : ℝ → HermitianField M) (p q : M.Carrier) (a K r τ σ rIn rOut : ℝ)
    (hK : 0 < K) (hr : 0 < r) (hτ : 0 < τ) (hσ : 0 < σ)
    (hflow : LocalRealRicciFlow h (distBall (h a) p (2*r)) (Set.Icc a (a+2*τ)) σ)
    (hcurv : ∀ x ∈ distBall (h a) p (2*r), ∀ t ∈ Set.Icc a (a+2*τ),
      curvatureJetNorm (h t) 0 x≤K)
    (hIn : 0 < rIn) (hInOut : rIn < rOut) (hOut : rOut≤2*r)
    (hq : q∈distBall (h a) p rIn)
    (y : M.Carrier) (hy : y∉interior (fieldDistanceBuffer (h a) p rIn rOut))
    (t : ℝ) (ht : t∈Set.Icc a (a+2*τ)) :
    timeDistanceCutoff h q (Real.exp (-σ*(2*n : ℕ)*K*τ)*(rOut-rIn)/4) y t=0 := by
  apply continuous_cutoff_zero_on_boundary _ _
    (timeDistanceCutoff_continuous_slice h hflow.1 q _ ht) _ y hy
  intro z hz
  exact local_flow_timeDistanceCutoff_nonzero_mem_buffer h p q a K r τ σ rIn rOut
    hK hr hτ hσ hflow hcurv hIn hInOut hOut hq z t ht hz

theorem jet_distanceCutoff_bernstein_step
    (h : ℝ → HermitianField M) (p q : M.Carrier) (a K r τ σ rIn rOut b₀ T B : ℝ)
    (hK : 0 < K) (hr : 0 < r) (hτ : 0 < τ) (hσ : 0 < σ)
    (hO : IsOpen (distBall (h a) p (2*r)))
    (hcO : IsCompact (closure (distBall (h a) p (2*r))))
    (hflow : LocalRealRicciFlow h (distBall (h a) p (2*r)) (Set.Icc a (a+2*τ)) σ)
    (hcurv : ∀ x ∈ distBall (h a) p (2*r), ∀ t ∈ Set.Icc a (a+2*τ),
      curvatureJetNorm (h t) 0 x≤K)
    (hIn : 0 < rIn) (hInOut : rIn < rOut) (hOut : rOut≤2*r)
    (hq : q∈distBall (h a) p rIn) (hab₀ : a≤b₀) (hb₀T : b₀<T)
    (hT : T<a+2*τ) (hB : 1≤B) (k : ℕ)
    (hLower : ∀ x ∈ distBall (h a) p rOut, ∀ t ∈ Set.Icc b₀ T,
      ∀ j≤k, jetSq (h t) j x≤B)
    (hSupports : ParabolicCutoffLowerSupports h σ
      (timeDistanceCutoff h q (Real.exp (-σ*(2*n : ℕ)*K*τ)*(rOut-rIn)/4))
      (fieldDistanceBuffer (h a) p rIn rOut) b₀ T
      (16/(Real.exp (-σ*(2*n : ℕ)*K*τ)*(rOut-rIn)/4)^2)
      (σ*(2*(2*n : ℕ)/(Real.exp (-σ*(2*n : ℕ)*K*τ)*(rOut-rIn)/4)^2+
        (8/3 : ℝ)*(2*n : ℕ)*K))) :
    jetSq (h T) (k+1) q≤
      bernsteinStepBound n (k+1) K σ (Real.exp (-σ*(2*n : ℕ)*K*τ)*(rOut-rIn)/4)
        (T-b₀) B (jetEvolutionConstant n (k+1)) (jetEvolutionConstant n k) := by
  let R := Real.exp (-σ*(2*n : ℕ)*K*τ)*(rOut-rIn)/4
  let S := fieldDistanceBuffer (h a) p rIn rOut
  have ha : a ∈ Set.Icc a (a+2*τ) := ⟨le_rfl,by linarith⟩
  have htime {t : ℝ} (ht : t∈Set.Icc b₀ T) : t∈Set.Icc a (a+2*τ) :=
    ⟨hab₀.trans ht.1,ht.2.trans hT.le⟩
  have hS := fieldDistanceBuffer_isCompact (h a) (metricFamilySmooth_slice h hflow.1 ha)
    p hIn hInOut hOut hcO
  have hSr := fieldDistanceBuffer_subset_outerBall (h a) p hIn hInOut
  have hSO : S ⊆ distBall (h a) p (2*r) := by
    intro x hx
    apply (mem_distBall_iff (h a) p x (by positivity)).mpr
    exact ((mem_distBall_iff (h a) p x (hIn.trans hInOut)).mp (hSr hx)).trans_le hOut
  have hη := local_flow_timeDistanceCutoff_continuousOn h p q a K r τ σ rIn rOut
    hK hr hτ hσ hflow hcurv hIn hInOut hOut hq
  have hh := jet_bernstein_local_step h (distBall (h a) p (2*r)) S a (a+2*τ) σ b₀ T B
    (16/R^2) (σ*(2*(2*n : ℕ)/R^2+(8/3 : ℝ)*(2*n : ℕ)*K)) hO hS hSO
    (by linarith) hab₀ hb₀T hT hσ hB (by positivity) (by positivity) hflow k
    (timeDistanceCutoff h q R)
    (hη.mono (fun _ hp => ⟨Set.mem_univ _,htime hp.2⟩))
    (fun x _ t _ => ⟨timeDistanceCutoff_nonneg h q R x t,timeDistanceCutoff_le_one h q R x t⟩)
    (fun x _ hx t ht => local_flow_timeDistanceCutoff_zero_on_buffer_boundary h p q
      a K r τ σ rIn rOut hK hr hτ hσ hflow hcurv hIn hInOut hOut hq x hx t (htime ht))
    hSupports (fun x hx t ht _ => hLower x (hSr (interior_subset hx)) t ⟨ht.1.le,ht.2⟩)
    q (innerBall_subset_fieldDistanceBuffer (h a) p hIn hInOut hq)
      (timeDistanceCutoff_center h hflow.1 q R (htime ⟨hb₀T.le,le_rfl⟩))
  refine hh.trans ?_
  have hbb : 0<B := by linarith
  simpa only [Nat.add_sub_cancel,Nat.add_assoc] using
    bernsteinScalarBound_le_stepBound n (k+1) K σ R (T-b₀) B hσ hbb (sub_pos.mpr hb₀T)

end Yau.LeafProofs.L23Aux
