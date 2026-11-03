import Yau.LeafProofs.L16SpatialTransport

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem schauderBound_congr_cylinder_univ {n : ℕ} {α T C : ℝ} {u v : Point n → ℝ}
    (hu : SchauderBound α (cylinder Set.univ 0 T) u C)
    (hEq : Set.EqOn u v (cylinder Set.univ 0 T)) :
    SchauderBound α (cylinder Set.univ 0 T) v C := by
  refine ⟨c2_congr_cylinder_univ hu.1 hEq,hu.2.1,?_,?_,?_⟩
  · intro p hp
    rw [← hEq hp,← spatialD_congr_cylinder_univ hEq hp]
    exact hu.2.2.1 p hp
  · exact holderBound_congr_on hu.2.2.2.1 (fun p hp => spatialDD_congr_cylinder_univ hEq hp)
  · exact holderBound_congr_on hu.2.2.2.2 (fun p hp => timeD_congr_on hEq hp)

theorem lowPair_holderBound_congr_cylinder_univ {n : ℕ} {α T C : ℝ} {u v : Point n → ℝ}
    (hu : HolderBound α (cylinder Set.univ 0 T) (fun p => (u p,spatialD u p)) C)
    (hEq : Set.EqOn u v (cylinder Set.univ 0 T)) :
    HolderBound α (cylinder Set.univ 0 T) (fun p => (v p,spatialD v p)) C :=
  holderBound_congr_on hu (fun _ hp => Prod.ext (hEq hp) (spatialD_congr_cylinder_univ hEq hp))

/-- The genuine directional derivative is itself a global Schauder solution.
The proof identifies it using uniform residual convergence and supremum stability. -/
theorem spatialPartial_schauder_of_holder_derivatives {n : ℕ} {α T U M0 M1 F1 L lam upper : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hL : 0 ≤ L)
    {u f : Point n → ℝ} {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hu : SchauderBound α (cylinder Set.univ 0 T) u U)
    (huLow : HolderBound α (cylinder Set.univ 0 T) (fun p => (u p,spatialD u p)) U)
    (hInit : ∀ x, u (x,0) = 0)
    (hOp : ∀ p ∈ cylinder Set.univ 0 T, linearOp (cylinder Set.univ 0 T) a b u p = f p)
    (ha : HolderBound α (cylinder Set.univ 0 T) a M0)
    (hb : ∀ i, HolderBound α (cylinder Set.univ 0 T) (fun p => b p i) M0)
    (hLip : ∀ p ∈ cylinder Set.univ 0 T, ∀ q ∈ cylinder Set.univ 0 T, ‖a p-a q‖ ≤ L*‖p-q‖)
    (hEll : Elliptic (cylinder Set.univ 0 T) a lam upper)
    {K : Set (Space n)} (hK : IsCompact K)
    (hExterior : ∀ p ∈ cylinder Set.univ 0 T, p.1 ∉ K → a p = 1)
    (e : Space n)
    (hDa : HolderBound α (cylinder Set.univ 0 T) (spatialPartial a e) M1)
    (hDb : ∀ i, HolderBound α (cylinder Set.univ 0 T) (spatialPartial (fun p => b p i) e) M1)
    (hDf : HolderBound α (cylinder Set.univ 0 T) (spatialPartial f e) F1)
    (hDiffa : ∀ p ∈ cylinder Set.univ 0 T, DifferentiableAt ℝ (fun x => a (x,p.2)) p.1)
    (hDiffb : ∀ i, ∀ p ∈ cylinder Set.univ 0 T, DifferentiableAt ℝ (fun x => b (x,p.2) i) p.1)
    (hDifff : ∀ p ∈ cylinder Set.univ 0 T, DifferentiableAt ℝ (fun x => f (x,p.2)) p.1) :
    ∃ D : ℝ, SchauderBound α (cylinder Set.univ 0 T) (spatialPartial u e) D ∧
      HolderBound α (cylinder Set.univ 0 T)
        (fun p => (spatialPartial u e p,spatialD (spatialPartial u e) p)) D ∧
      (∀ x, spatialPartial u e (x,0) = 0) ∧
      ∀ p ∈ cylinder Set.univ 0 T, linearOp (cylinder Set.univ 0 T) a b (spatialPartial u e) p =
        linearizedSpatialSource e u a b f p := by
  have hH := linearizedSpatialSource_holderBound e hu huLow hDa hDb hDf
  obtain ⟨z,Z,hz,hzLow,hz0,hzOp⟩ := bounded_holder_global_classical_solution hα hα1 hT hL
    ha hb hH hLip hEll hK hExterior
  have hIdent : Set.EqOn (spatialPartial u e) z (cylinder Set.univ 0 T) := by
    apply spatialPartial_eq_of_residual_approximation hα hT ha.1 hH.1 hu.1 hz.1 hEll
      (fun p hp i => by simpa only [Real.norm_eq_abs] using (hb i).2.1 p hp)
      (fun p hp => (hu.2.2.1 p hp).1) (fun p hp => (hz.2.2.1 p hp).1)
      hInit hz0 e (fun h _ => c2_spatialDifferenceQuotient hu.1 e h)
    intro h hh p hp
    have hpQ : p ∈ cylinder Set.univ 0 T := ⟨Set.mem_univ _,hp.2.1.le,hp.2.2⟩
    rw [linearOp_spatialDifferenceQuotient hu.1 hOp e h hpQ,hzOp p hpQ]
    exact quotientSpatialSource_sub_bound hα e hu huLow hDa hDb hDf hDiffa hDiffb hDifff hpQ hh.ne'
  have hIdent' : Set.EqOn z (spatialPartial u e) (cylinder Set.univ 0 T) := fun p hp => (hIdent hp).symm
  refine ⟨Z,schauderBound_congr_cylinder_univ hz hIdent',
    lowPair_holderBound_congr_cylinder_univ hzLow hIdent',?_,?_⟩
  · intro x
    exact (hIdent ⟨Set.mem_univ _,le_rfl,hT.le⟩).trans (hz0 x)
  · intro p hp
    rw [linearOp_congr_cylinder_univ hIdent a b hp,hzOp p hp]

theorem smooth_compact_derivative_common_bounds {n : ℕ} {α T : ℝ}
    (hT : 0 < T) (hα : 0 < α) (hα1 : α < 1) {K : Set (Space n)} (hK : IsCompact K)
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {f : Point n → ℝ}
    (hSmooth : SmoothCoefficients (cylinder Set.univ 0 T) a b)
    (hfSmooth : ContDiffOn ℝ ∞ f (cylinder Set.univ 0 T))
    (hExterior : ∀ x ∉ K, ∀ t ∈ Set.Icc 0 T,
      a (x,t) = 1 ∧ b (x,t) = 0 ∧ f (x,t) = 0) (e : Space n) :
    ∃ M F : ℝ, 0 < M ∧ 0 < F ∧
      HolderBound α (cylinder Set.univ 0 T) (spatialPartial a e) M ∧
      (∀ i, HolderBound α (cylinder Set.univ 0 T) (spatialPartial (fun p => b p i) e) M) ∧
      HolderBound α (cylinder Set.univ 0 T) (spatialPartial f e) F := by
  have hA : ∃ C : ℝ, 0 < C ∧ HolderBound α (cylinder Set.univ 0 T) (spatialPartial a e) C := by
    simpa only [spatialWordDerivative] using smooth_cylinder_spatialWordDerivative_holder hT hα hα1 hK hSmooth.1
      (fun x hx t ht => (hExterior x hx t ht).1) [e]
  obtain ⟨CA,hCA,hDa⟩ := hA
  have hB (i : Yau.RIdx n) : ∃ C : ℝ, 0 < C ∧
      HolderBound α (cylinder Set.univ 0 T) (spatialPartial (fun p => b p i) e) C := by
    simpa only [spatialWordDerivative] using smooth_cylinder_spatialWordDerivative_holder hT hα hα1 hK
      (hSmooth.2 i) (c := (0 : ℝ)) (fun x hx t ht => by rw [(hExterior x hx t ht).2.1]; rfl) [e]
  choose CB hCB hDb using hB
  have hF : ∃ C : ℝ, 0 < C ∧ HolderBound α (cylinder Set.univ 0 T) (spatialPartial f e) C := by
    simpa only [spatialWordDerivative] using smooth_cylinder_spatialWordDerivative_holder hT hα hα1 hK hfSmooth
      (fun x hx t ht => (hExterior x hx t ht).2.2) [e]
  obtain ⟨F,hF,hDf⟩ := hF
  let M : ℝ := 1+CA+∑ i : Yau.RIdx n, CB i
  have hSum : 0 ≤ ∑ i : Yau.RIdx n, CB i := Finset.sum_nonneg (fun i _ => (hCB i).le)
  have hM : 0 < M := by dsimp only [M]; linarith
  have hCAM : CA ≤ M := by dsimp only [M]; linarith
  have hCBM (i : Yau.RIdx n) : CB i ≤ M := by
    have hi := Finset.single_le_sum (s := Finset.univ) (f := CB)
      (fun j _ => (hCB j).le) (Finset.mem_univ i)
    dsimp only [M]
    linarith
  exact ⟨M,F,hM,hF,holderBound_mono_const hDa hCAM,
    fun i => holderBound_mono_const (hDb i) (hCBM i),hDf⟩

theorem smooth_compact_first_spatial_derivative_schauder {n : ℕ} {α T U lam upper : ℝ}
    (hT : 0 < T) (hα : 0 < α) (hα1 : α < 1)
    {u f : Point n → ℝ} {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hSmooth : SmoothCoefficients (cylinder Set.univ 0 T) a b)
    (hfSmooth : ContDiffOn ℝ ∞ f (cylinder Set.univ 0 T))
    (hEll : Elliptic (cylinder Set.univ 0 T) a lam upper)
    {K : Set (Space n)} (hK : IsCompact K)
    (hExterior : ∀ x ∉ K, ∀ t ∈ Set.Icc 0 T,
      a (x,t) = 1 ∧ b (x,t) = 0 ∧ f (x,t) = 0)
    (hu : SchauderBound α (cylinder Set.univ 0 T) u U)
    (huLow : HolderBound α (cylinder Set.univ 0 T) (fun p => (u p,spatialD u p)) U)
    (hInit : ∀ x, u (x,0) = 0)
    (hOp : ∀ p ∈ cylinder Set.univ 0 T, linearOp (cylinder Set.univ 0 T) a b u p = f p)
    (e : Space n) :
    ∃ D : ℝ, SchauderBound α (cylinder Set.univ 0 T) (spatialPartial u e) D ∧
      HolderBound α (cylinder Set.univ 0 T)
        (fun p => (spatialPartial u e p,spatialD (spatialPartial u e) p)) D ∧
      (∀ x, spatialPartial u e (x,0) = 0) ∧
      ∀ p ∈ cylinder Set.univ 0 T, linearOp (cylinder Set.univ 0 T) a b (spatialPartial u e) p =
        linearizedSpatialSource e u a b f p := by
  obtain ⟨M0,L,hM0,hL,ha,hb,hLip⟩ := smooth_coefficients_common_bounds hT hα hα1 hK hSmooth
    (fun x hx t ht => ⟨(hExterior x hx t ht).1,(hExterior x hx t ht).2.1⟩)
  obtain ⟨M1,F1,hM1,hF1,hDa,hDb,hDf⟩ := smooth_compact_derivative_common_bounds hT hα hα1 hK hSmooth hfSmooth hExterior e
  exact spatialPartial_schauder_of_holder_derivatives hα hα1 hT hL.le hu huLow hInit hOp ha hb hLip hEll hK
    (fun p hp hx => (hExterior p.1 hx p.2 hp.2).1) e hDa hDb hDf
    (fun p hp => (cylinder_spatialSlice_contDiff hSmooth.1 hp.2).differentiable (by simp) p.1)
    (fun i p hp => (cylinder_spatialSlice_contDiff (hSmooth.2 i) hp.2).differentiable (by simp) p.1)
    (fun p hp => (cylinder_spatialSlice_contDiff hfSmooth hp.2).differentiable (by simp) p.1)

end Yau.LeafProofs.L16Aux
