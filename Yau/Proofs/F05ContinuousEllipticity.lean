import Yau.Proofs.F05LinearEllipticity
import Yau.Proofs.F05FlowPatchSolver
import Yau.Proofs.F05RegionGeometry

/-! An actual positive continuous scalar coefficient on the closed physical
charts gives common ellipticity; no smoothness of the unknown is assumed. -/

open Set
open scoped Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_continuous_coefficient_elliptic {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) (c : M.Carrier → ℝ → ℝ)
    {T : ℝ} (hT : 0 ≤ T) (hh : MetricFamilySmooth h (Icc 0 T))
    (hc : ∀ i, ContinuousOn (pull A i c) (F05Q A i T))
    (hPos : ∀ i, ∀ q ∈ F05Q A i T, 0 < pull A i c q) :
    ∃ lam upper : ℝ, ∀ i, Elliptic (F05Q A i T) (F05FlowPrincipal A i h c) lam upper := by
  have hEach (i : Fin A.count) : ∃ lam upper : ℝ,
      Elliptic (F05Q A i T) (F05FlowPrincipal A i h c) lam upper := by
    have hSub : F05D A i ⊆ Metric.closedBall 0 2 := fun z hz =>
      by simpa only [Metric.mem_closedBall,dist_zero_right] using hz.1
    have hD : IsCompact (F05D A i) :=
      (isCompact_closedBall (0 : Space n) 2).of_isClosed_subset (F05D_isClosed A i) hSub
    obtain ⟨z,hz⟩ := F05D_interior_nonempty A i
    have hNE : (F05Q A i T).Nonempty := ⟨(z,0),interior_subset hz,le_rfl,hT⟩
    obtain ⟨l,b,hl,hlb,hBounds⟩ := F05_compact_positive_bounds (hD.prod isCompact_Icc) hNE (hc i) (hPos i)
    obtain ⟨lam,upper,hBase⟩ := F05_flat_principal_elliptic_chart hA h hh i
    have hBaseQ : Elliptic (F05Q A i T) (fun q => flatA (h q.2) A i q) lam upper :=
      ⟨hBase.1,hBase.2.1,fun q hq => hBase.2.2 q ⟨hSub hq.1,hq.2⟩⟩
    exact ⟨l*lam,b*upper,F05_elliptic_scalar_mul hBaseQ hl hlb hBounds⟩
  exact F05_uniform_elliptic_family (fun i => F05Q A i T) (fun i => F05FlowPrincipal A i h c) hEach

end Yau.Proofs.F05Aux
