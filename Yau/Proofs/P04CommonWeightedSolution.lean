import Yau.Proofs.P04HilbertMultiplier
import Yau.Proofs.P04PoleConstraint
import Yau.LeafProofs.L14Exact

noncomputable section
open Set Filter MeasureTheory Bundle
open scoped Topology Manifold ContDiff ENNReal

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs BundleDbar
variable {n : ℕ} {M : ComplexManifold n}

theorem ofReal_normSq_le_iff {H : Type*} [SeminormedAddCommGroup H]
    (v : H) {B : ℝ} (hB : 0 ≤ B) :
    ENNReal.ofReal (‖v‖^2) ≤ ENNReal.ofReal B ↔ ‖v‖ ≤ Real.sqrt B := by
  constructor
  · intro h
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    rw [ENNReal.toReal_ofReal (sq_nonneg _),ENNReal.toReal_ofReal hB] at ht
    exact Real.le_sqrt_of_sq_le ht
  · intro h
    apply ENNReal.ofReal_le_ofReal
    nlinarith [Real.sq_sqrt hB,Real.sqrt_nonneg B,norm_nonneg v]

/-- Genuine smooth-weight L14 solutions produce one actual solution with
all regularized bounds, by a strong limit in the common Hilbert space. -/
theorem exists_common_weighted_solution (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (Φ : M.Carrier → ℝ) (hΦ : SmoothFn Φ)
    (P : ℕ → M.Carrier → ℝ) (hP : ∀ j, SmoothFn (P j))
    (hcP : ∀ j, HasCompactSupport (P j)) (hnonpos : ∀ j x, P j x ≤ 0)
    (hanti : ∀ x, Antitone (fun j => P j x))
    (hN : ∀ j, WeightedNakanoNonnegative (r := 1) (CanonicalCoefficients M) flatMetric
      (fun x => Φ x+P j x))
    (f : NQForm (CanonicalCoefficients M) 1)
    (hf : WeightedL2 (r := 1) (CanonicalCoefficients M) g.form flatMetric μ Φ f)
    (hclosed : WeaklyClosed (r := 1) (CanonicalCoefficients M) f)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ j, inverseCurvatureIntegral (r := 1) (CanonicalCoefficients M) g.form flatMetric μ
      (fun x => Φ x+P j x) f ≤ ENNReal.ofReal B) :
    ∃ u : NQForm (CanonicalCoefficients M) 0,
      WeakDbar (r := 1) (CanonicalCoefficients M) u f ∧
      WeightedL2 (r := 1) (CanonicalCoefficients M) g.form flatMetric μ Φ u ∧
      ∀ j, weightedNormSq (r := 1) (CanonicalCoefficients M) g.form flatMetric μ
        (fun x => Φ x+P j x) u ≤ ENNReal.ofReal B := by
  classical
  let H := L14Aux.WeightedTopHilbert (CanonicalCoefficients M) g μ hμ flatMetric flatMetric_smooth Φ hΦ
  letI : InnerProductSpace ℝ H := InnerProductSpace.complexToReal
  let F : L14Aux.WeightedOneSection (CanonicalCoefficients M) g μ hμ flatMetric flatMetric_smooth Φ hΦ := ⟨f,hf⟩
  let R := fun v : H => L14Aux.weightedTopHilbertRepresentative (CanonicalCoefficients M) g μ hμ
    flatMetric flatMetric_smooth Φ hΦ v
  choose T hT using fun j => exists_poleHilbertMultiplier g μ hμ Φ hΦ (P j) (hP j) (hcP j)
  let C : ℕ → Set H := fun j => canonicalPoleConstraint g μ hμ Φ hΦ F (T j) (Real.sqrt B)
  have hnorm_iff (j : ℕ) (v : H) :
      weightedNormSq (r := 1) (CanonicalCoefficients M) g.form flatMetric μ
        (fun x => Φ x+P j x) (R v).1 ≤ ENNReal.ofReal B ↔ ‖T j v‖ ≤ Real.sqrt B := by
    rw [← hT j v]
    exact ofReal_normSq_le_iff _ hB
  have hmem (j : ℕ) (v : H) : v ∈ C j ↔
      v ∈ canonicalDbarSlice g μ hμ Φ hΦ F ∧ ‖T j v‖ ≤ Real.sqrt B := by
    change (_ ∧ dist (T j v) 0 ≤ Real.sqrt B) ↔ _
    rw [dist_zero_right]
  have hne (j : ℕ) : (C j).Nonempty := by
    have hφ : SmoothFn (fun x => Φ x+P j x) := fun a => (hΦ a).add (hP j a)
    obtain ⟨u,hu,hdu,hnorm⟩ := L14Aux.weightedDbarEstimate (CanonicalCoefficients M)
      g μ flatMetric (fun x => Φ x+P j x) hμ coefficient_holomorphic flatMetric_smooth hφ
      (hN j) f hclosed ((hbound j).trans_lt ENNReal.ofReal_lt_top)
    have huΦ := weightedL2_of_larger_weight g.form μ (φ := fun x => Φ x+P j x) (ψ := Φ)
      (fun x => by linarith [hnonpos j x]) u hu
    let U : L14Aux.WeightedTopSection (CanonicalCoefficients M) g μ hμ flatMetric flatMetric_smooth Φ hΦ := ⟨u,huΦ⟩
    let v : H := L14Aux.realizeWeightedTopSection (CanonicalCoefficients M) g μ hμ
      flatMetric flatMetric_smooth Φ hΦ U
    have hae : ∀ᵐ x ∂μ, u x=(R v).1 x := by
      apply (L14Aux.realizeWeightedTopSection_eq_iff_ae (CanonicalCoefficients M) g μ hμ
        flatMetric flatMetric_smooth Φ hΦ U (R v)).mp
      exact (L14Aux.weightedTopHilbertRepresentative_realize (CanonicalCoefficients M) g μ hμ
        flatMetric flatMetric_smooth Φ hΦ v).symm
    refine ⟨v,(hmem j v).mpr ⟨?_,?_⟩⟩
    · apply (canonicalDbarSlice_mem_iff g μ hμ Φ hΦ F v).mpr
      exact L14Aux.weakDbar_of_ae_eq (CanonicalCoefficients M) g μ hμ u (R v).1 f f hae
        (Eventually.of_forall (fun _ => rfl)) hdu
    · apply (hnorm_iff j v).mp
      rw [← L14Aux.weightedNormSq_congr_ae (CanonicalCoefficients M) g.form flatMetric μ
        (fun x => Φ x+P j x) u (R v).1 hae]
      exact hnorm.trans (hbound j)
  have hnested : Antitone C := by
    intro j l hjl v hv
    obtain ⟨hvs,hvl⟩ := (hmem l v).mp hv
    apply (hmem j v).mpr
    refine ⟨hvs,(hnorm_iff j v).mp ?_⟩
    calc
      _ ≤ weightedNormSq (r := 1) (CanonicalCoefficients M) g.form flatMetric μ
          (fun x => Φ x+P l x) (R v).1 :=
        weightedNormSq_antitone_weight g.form μ
          (fun x => by linarith [hanti x hjl]) (R v).1
      _ ≤ _ := (hnorm_iff l v).mpr hvl
  have hbounded (j : ℕ) (v : H) (hv : v ∈ C j) : ‖v‖ ≤ Real.sqrt B := by
    apply (ofReal_normSq_le_iff v hB).mp
    rw [← L14Aux.weightedTopHilbertRepresentative_normSq (CanonicalCoefficients M) g μ hμ
      flatMetric flatMetric_smooth Φ hΦ v]
    calc
      _ ≤ weightedNormSq (r := 1) (CanonicalCoefficients M) g.form flatMetric μ
          (fun x => Φ x+P j x) (R v).1 :=
        weightedNormSq_antitone_weight g.form μ (fun x => by linarith [hnonpos j x]) (R v).1
      _ ≤ _ := (hnorm_iff j v).mpr ((hmem j v).mp hv).2
  obtain ⟨v,hv⟩ := exists_mem_all_nested_closed_convex C hne
    (fun j => canonicalPoleConstraint_isClosed g μ hμ Φ hΦ F (T j) (Real.sqrt B))
    (fun j => canonicalPoleConstraint_convex g μ hμ Φ hΦ F (T j) (Real.sqrt B))
    hnested (Real.sqrt B) hbounded
  exact ⟨(R v).1,(canonicalDbarSlice_mem_iff g μ hμ Φ hΦ F v).mp ((hmem 0 v).mp (hv 0)).1,
    (R v).2,fun j => (hnorm_iff j v).mpr ((hmem j v).mp (hv j)).2⟩

end Yau.Proofs.P04Aux
