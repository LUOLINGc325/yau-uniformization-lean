import Yau.Proofs.E02NormQuadraticJet
import Yau.Proofs.E02InfSemiconcavity
import Yau.Proofs.E02ProjectionNull
import Yau.LeafProofs.L01

open Set Filter Asymptotics MeasureTheory
open scoped Topology Asymptotics InnerProductSpace
noncomputable section
namespace Yau.NodeProofs.E02Aux

theorem compactInfConvolution_ae_realSecondJet {d : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin d))) (v : EuclideanSpace ℝ (Fin d) → ℝ)
    (hK : IsCompact K) (hne : K.Nonempty) (hv : LowerSemicontinuousOn v K)
    (hv0 : ∀ a ∈ K, 0 ≤ v a) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᵐ q ∂volume, ∃ p A, RealSecondJet (compactInfConvolution K v κ) q p A := by
  have hConc := compactInfConvolution_sub_quadratic_concave K v hK hne hv hv0 hκ
  have hConv : ConvexOn ℝ univ
      (fun q => ‖q‖^2/(2*κ)-compactInfConvolution K v κ q) := by
    refine ⟨convex_univ,?_⟩
    intro x _ y _ a b ha hb hab
    have h := hConc.2 (mem_univ x) (mem_univ y) ha hb hab
    simp only [smul_eq_mul] at h ⊢
    linarith
  have hAlex := Yau.LeafProofs.L01 d univ
    (fun q => ‖q‖^2/(2*κ)-compactInfConvolution K v κ q) isOpen_univ hConv
  have hAE : ∀ᵐ q ∂volume, ∃ p A,
      RealSecondJet (fun y => ‖y‖^2/(2*κ)-compactInfConvolution K v κ y) q p A := by
    simpa only [Measure.restrict_univ,RealSecondJet] using hAlex
  filter_upwards [hAE] with q hq
  obtain ⟨p,A,hqJet⟩ := hq
  have hQuad := realSecondJet_norm_sq_div_two κ q
  have hSub := realSecondJet_sub hQuad hqJet
  have hFun : (fun y => ‖y‖^2/(2*κ)-(‖y‖^2/(2*κ)-compactInfConvolution K v κ y)) =
      compactInfConvolution K v κ := by funext y; ring
  rw [hFun] at hSub
  exact ⟨_,_,hSub⟩

/-- Registered native Aleksandrov plus the genuine projection null lemma
constructs all factor jets at ONE shared base/time product point. -/
theorem compactInfConvolution_simultaneous_jets (n m : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin (4*n+1))))
    (v : EuclideanSpace ℝ (Fin (4*n+1)) → ℝ)
    (hK : IsCompact K) (hne : K.Nonempty) (hv : LowerSemicontinuousOn v K)
    (hv0 : ∀ a ∈ K, 0 ≤ v a) {κ : ℝ} (hκ : 0 < κ)
    (S : Set (EuclideanSpace ℝ (Fin (2*n+1+2*n*m)))) (hS : 0 < volume S) :
    ∃ Q ∈ S, ∃ (p : Fin m → EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ] ℝ)
      (A : Fin m → EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ]
        EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ] ℝ),
      ∀ i, RealSecondJet (compactInfConvolution K v κ) (factorProjection n m i Q) (p i) (A i) := by
  let N := {q | ¬∃ p A, RealSecondJet (compactInfConvolution K v κ) q p A}
  have hN : volume N = 0 := ae_iff.mp (compactInfConvolution_ae_realSecondJet K v hK hne hv hv0 hκ)
  obtain ⟨Q,hQ,hGood⟩ := exists_simultaneous_good_projection n m S hS N hN
  have hAll : ∀ i : Fin m, ∃ p A,
      RealSecondJet (compactInfConvolution K v κ) (factorProjection n m i Q) p A := by
    intro i
    exact not_not.mp (hGood i)
  choose p A hJet using hAll
  exact ⟨Q,hQ,p,A,hJet⟩

end Yau.NodeProofs.E02Aux
