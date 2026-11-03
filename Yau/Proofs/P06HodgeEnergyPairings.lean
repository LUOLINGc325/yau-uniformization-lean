import Yau.Proofs.P06HodgeEnergySpace

noncomputable section
open MeasureTheory
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03
variable {n k : ℕ} {M : ComplexManifold n}

theorem realizeActualForm_inner (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A B : RealForm M k) (hA : L2RealForm g.form μ A) (hB : L2RealForm g.form μ B) :
    inner ℝ (realizeActualForm g μ A hA) (realizeActualForm g μ B hB) =
      ∫ y, formInner g.form A B y ∂μ := realizeL2Form_inner g μ _ _

theorem hodgeEnergy_pairing_of_core {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (P : HodgeEnergyAmbient g μ →L[ℝ] V) (b : V) (c : L2FormHilbert g μ 2)
    (hcore : ∀ (A : RealForm M 2) (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A),
      inner ℝ (P (hodgeEnergyCoreTuple g μ hμ A hA hcA)) b =
        inner ℝ (hodgeEnergyCoreTuple g μ hμ A hA hcA).fst c)
    (u : HodgeEnergySpace g μ hμ) :
    inner ℝ (P (u : HodgeEnergyAmbient g μ)) b = inner ℝ (hodgeEnergyValue g μ hμ u) c := by
  let L : HodgeEnergyAmbient g μ →L[ℝ] ℝ :=
    (innerSL ℝ b).comp P - (innerSL ℝ c).comp (WithLp.fstL 2 ℝ _ _)
  have hs : Submodule.span ℝ (hodgeEnergyCoreSet g μ hμ) ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro p ⟨A, hA, hcA, rfl⟩
    change inner ℝ b (P (hodgeEnergyCoreTuple g μ hμ A hA hcA)) -
      inner ℝ c (hodgeEnergyCoreTuple g μ hμ A hA hcA).fst = 0
    rw [real_inner_comm (P (hodgeEnergyCoreTuple g μ hμ A hA hcA)) b,
      real_inner_comm (hodgeEnergyCoreTuple g μ hμ A hA hcA).fst c]
    exact sub_eq_zero.mpr (hcore A hA hcA)
  have hclosure : hodgeEnergySubmodule g μ hμ ≤ L.ker :=
    (Submodule.span ℝ (hodgeEnergyCoreSet g μ hμ)).topologicalClosure_minimal hs L.isClosed_ker
  have heq := hclosure u.property
  change inner ℝ b (P (u : HodgeEnergyAmbient g μ)) - inner ℝ c (hodgeEnergyValue g μ hμ u) = 0 at heq
  rw [real_inner_comm (P (u : HodgeEnergyAmbient g μ)) b,
    real_inner_comm (hodgeEnergyValue g μ hμ u) c] at heq
  exact sub_eq_zero.mp heq

theorem hodgeEnergy_exterior_pairing (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (u : HodgeEnergySpace g μ hμ)
    (B : RealForm M 3) (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B) :
    inner ℝ (hodgeEnergyExterior g μ hμ u)
      (realizeActualForm g μ B (smooth_compactlySupported_l2RealForm g μ hμ B hB hcB)) =
    inner ℝ (hodgeEnergyValue g μ hμ u)
      (realizeActualForm g μ (codifferentialRealForm g.form B) (codifferentialRealForm_l2 g μ hμ B hB hcB)) := by
  apply hodgeEnergy_pairing_of_core g μ hμ ((WithLp.fstL 2 ℝ _ _).comp (WithLp.sndL 2 ℝ _ _))
  intro A hA hcA
  change inner ℝ (realizeActualForm g μ (exteriorRealForm A) _) (realizeActualForm g μ B _) =
    inner ℝ (realizeActualForm g μ A _) (realizeActualForm g μ (codifferentialRealForm g.form B) _)
  rw [realizeActualForm_inner, realizeActualForm_inner]
  exact integral_exterior_codifferential g μ hμ A B hA hB hcA

theorem hodgeEnergy_lower_pairing (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (u : HodgeEnergySpace g μ hμ)
    (B : RealForm M 1) (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B) :
    inner ℝ (hodgeEnergyLower g μ hμ u)
      (realizeActualForm g μ B (smooth_compactlySupported_l2RealForm g μ hμ B hB hcB)) =
    inner ℝ (hodgeEnergyValue g μ hμ u)
      (realizeActualForm g μ (exteriorRealForm B) (exteriorRealForm_l2 g μ hμ B hB hcB)) := by
  apply hodgeEnergy_pairing_of_core g μ hμ ((WithLp.sndL 2 ℝ _ _).comp (WithLp.sndL 2 ℝ _ _))
  intro A hA hcA
  change inner ℝ (realizeActualForm g μ (codifferentialRealForm g.form A) _) (realizeActualForm g μ B _) =
    inner ℝ (realizeActualForm g μ A _) (realizeActualForm g μ (exteriorRealForm B) _)
  rw [real_inner_comm (realizeActualForm g μ B _) _,
    real_inner_comm (realizeActualForm g μ (exteriorRealForm B) _) _,
    realizeActualForm_inner, realizeActualForm_inner]
  exact (integral_exterior_codifferential g μ hμ B A hB hA hcB).symm

theorem realizeActualForm_zero (g : SmoothMetric M) (μ : Measure M.Carrier)
    (h0 : L2RealForm g.form μ (0 : RealForm M k)) : realizeActualForm g μ 0 h0 = 0 := by
  apply norm_eq_zero.mp
  have hs : ‖realizeActualForm g μ 0 h0‖ ^ 2 = 0 := by
    rw [realizeActualForm_norm_sq]
    simp only [formNormSq_zero, Pi.zero_apply, integral_zero]
  nlinarith [norm_nonneg (realizeActualForm g μ 0 h0)]

theorem hilbert_zero_of_compact_form_pairings (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (v : L2FormHilbert g μ k)
    (ht : ∀ B : RealForm M k, ∀ hB : SmoothRealForm B, ∀ hcB : CompactlySupportedRealForm B,
      inner ℝ v (realizeActualForm g μ B (smooth_compactlySupported_l2RealForm g μ hμ B hB hcB)) = 0) :
    v = 0 := by
  obtain ⟨A, hA, heA⟩ := l2FormHilbert_exists_section g μ v
  change realizeActualForm g μ A hA = v at heA
  have hae : ∀ᵐ y ∂μ, A y = (0 : RealForm M k) y := by
    apply l2Form_ae_eq_of_compact_pairings g μ hμ A 0 hA (l2RealForm_zero g.form μ)
    intro B hB hcB
    have hp := ht B hB hcB
    rw [← heA, realizeActualForm_inner] at hp
    simpa only [formInner_zero_left, Pi.zero_apply, integral_zero] using hp
  have he := (realizeL2Form_eq_iff_ae g μ (L2FormSpace.ofSection A hA)
    (L2FormSpace.ofSection 0 (l2RealForm_zero g.form μ))).mpr hae
  change realizeActualForm g μ A hA = realizeActualForm g μ 0 _ at he
  rw [heA, realizeActualForm_zero] at he
  exact he

theorem hodgeEnergyValue_injective (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) : Function.Injective (hodgeEnergyValue g μ hμ) := by
  intro u v huv
  let w := u - v
  have hJ : hodgeEnergyValue g μ hμ w = 0 := by
    simp only [w, map_sub, huv, sub_self]
  have hD : hodgeEnergyExterior g μ hμ w = 0 := by
    apply hilbert_zero_of_compact_form_pairings g μ hμ
    intro B hB hcB
    rw [hodgeEnergy_exterior_pairing g μ hμ w B hB hcB, hJ, inner_zero_left]
  have hδ : hodgeEnergyLower g μ hμ w = 0 := by
    apply hilbert_zero_of_compact_form_pairings g μ hμ
    intro B hB hcB
    rw [hodgeEnergy_lower_pairing g μ hμ w B hB hcB, hJ, inner_zero_left]
  have hn : ‖w‖ ^ 2 = 0 := by
    rw [hodgeEnergy_norm_sq, hJ, hodgeEnergy, hD, hδ]
    norm_num
  have hw : w = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg w])
  exact sub_eq_zero.mp hw

end Yau.NodeProofs.P06Aux
