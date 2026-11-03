import Yau.Blueprint.ParabolicSpaces
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false
open Set Filter Metric
open scoped Topology
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E]

theorem continuousRepresentative_weight_continuous {eta : ℝ} (heta : 0<eta) :
    Continuous (fun r : Point n × Point n => holderWeight eta r.1 r.2) := by
  exact ((continuous_fst.fst.sub continuous_snd.fst).norm.rpow_const (fun _ => Or.inr heta.le)).add
    ((continuous_fst.snd.sub continuous_snd.snd).abs.rpow_const (fun _ => Or.inr (by positivity)))

theorem continuousRepresentative_holder_uniformContinuousOn {S : Set (Point n)}
    {eta C : ℝ} (heta : 0<eta) (hC : 0≤C) (H : Point n → E)
    (hHolder : ∀ p∈S, ∀ q∈S, ‖H p-H q‖≤C*holderWeight eta p q) :
    UniformContinuousOn H S := by
  let w : ℝ → ℝ := fun d => C*(d^eta+d^(eta/2))
  have hw : ContinuousAt w 0 :=
    (continuous_const.mul ((Real.continuous_rpow_const heta.le).add
      (Real.continuous_rpow_const (by positivity)))).continuousAt
  have hw0 : w 0=0 := by simp [w,Real.zero_rpow heta.ne',Real.zero_rpow (by positivity : eta/2≠0)]
  apply Metric.uniformContinuousOn_iff.mpr
  intro eps heps
  obtain ⟨d,hd,hnear⟩ := Metric.continuousAt_iff.mp hw eps heps
  refine ⟨d,hd,?_⟩
  intro p hp q hq hpq
  have hsmall : w (dist p q)<eps := by
    have hh := hnear (x := dist p q) (by simpa only [Real.dist_eq,sub_zero,abs_of_nonneg dist_nonneg] using hpq)
    exact (le_abs_self _).trans_lt (by simpa only [hw0,Real.dist_eq,sub_zero] using hh)
  have hs : ‖p.1-q.1‖≤dist p q := by
    rw [dist_eq_norm]
    exact norm_fst_le (p-q)
  have ht : |p.2-q.2|≤dist p q := by
    rw [dist_eq_norm,←Real.norm_eq_abs]
    exact norm_snd_le (p-q)
  calc
    dist (H p) (H q)=‖H p-H q‖ := dist_eq_norm _ _
    _ ≤ C*holderWeight eta p q := hHolder p hp q hq
    _ ≤ w (dist p q) := by
      exact mul_le_mul_of_nonneg_left (add_le_add
        (Real.rpow_le_rpow (norm_nonneg _) hs heta.le)
        (Real.rpow_le_rpow (abs_nonneg _) ht (by positivity))) hC
    _ < eps := hsmall

theorem auto_dense_holder_representative [CompleteSpace E]
    {S K : Set (Point n)} (_hSK : S⊆K) (hDense : K⊆closure S)
    {eta C B : ℝ} (heta : 0<eta) (hC : 0≤C) (_hB : 0≤B)
    (H : Point n → E) (hBound : ∀ p∈S, ‖H p‖≤B)
    (hHolder : ∀ p∈S, ∀ q∈S, ‖H p-H q‖≤C*holderWeight eta p q) :
    ∃ Hbar : Point n → E, ContinuousOn Hbar K ∧ EqOn Hbar H S ∧
      (∀ p∈K, ‖Hbar p‖≤B) ∧
      (∀ p∈K, ∀ q∈K, ‖Hbar p-Hbar q‖≤C*holderWeight eta p q) := by
  classical
  let e : S → closure S := Set.inclusion subset_closure
  have he : IsUniformInducing e := (isUniformEmbedding_set_inclusion subset_closure).isUniformInducing
  have hd : DenseRange e := (denseRange_inclusion_iff subset_closure).mpr Subset.rfl
  let di : IsDenseInducing e := he.isDenseInducing hd
  have hUC := (continuousRepresentative_holder_uniformContinuousOn heta hC H hHolder).restrict
  let g : closure S → E := di.extend (fun p : S => H p)
  have hg : UniformContinuous g := uniformContinuous_uniformly_extend he hd hUC
  have hAgree : ∀ p : S, g (e p)=H p := uniformly_extend_of_ind he hd hUC
  let Hbar : Point n → E := fun p => if hp : p∈closure S then g ⟨p,hp⟩ else 0
  have hCont : ContinuousOn Hbar (closure S) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    change Continuous (fun p : closure S => Hbar p)
    have heq : (fun p : closure S => Hbar p)=g := by funext p; simp [Hbar]
    rw [heq]
    exact hg.continuous
  have hEq : EqOn Hbar H S := by
    intro p hp
    simpa [Hbar,subset_closure hp,e] using hAgree ⟨p,hp⟩
  have hBd : ∀ p∈closure S, ‖Hbar p‖≤B := by
    apply le_on_closure
    · intro p hp
      rw [hEq hp]
      exact hBound p hp
    · exact hCont.norm
    · exact continuousOn_const
  have hDiff : ContinuousOn (fun r : Point n × Point n => ‖Hbar r.1-Hbar r.2‖)
      (closure (S ×ˢ S)) := by
    rw [closure_prod_eq]
    exact ((hCont.comp continuousOn_fst (fun _ h => h.1)).sub
      (hCont.comp continuousOn_snd (fun _ h => h.2))).norm
  have hRhs : Continuous (fun r : Point n × Point n => C*holderWeight eta r.1 r.2) :=
    continuous_const.mul (continuousRepresentative_weight_continuous heta)
  have hRHSC : ContinuousOn (fun r : Point n × Point n => C*holderWeight eta r.1 r.2)
      (closure (S ×ˢ S)) := hRhs.continuousOn
  have hOn : ∀ r∈S ×ˢ S,
      ‖Hbar r.1-Hbar r.2‖≤C*holderWeight eta r.1 r.2 := by
    rintro ⟨x,y⟩ ⟨hx,hy⟩
    rw [hEq hx,hEq hy]
    exact hHolder x hx y hy
  have hHH : ∀ p∈closure S, ∀ q∈closure S,
      ‖Hbar p-Hbar q‖≤C*holderWeight eta p q := by
    intro p hp q hq
    have hmem : (p,q)∈closure (S ×ˢ S) := by
      rw [closure_prod_eq]
      exact ⟨hp,hq⟩
    exact le_on_closure hOn hDiff hRHSC hmem
  exact ⟨Hbar,hCont.mono hDense,hEq,fun p hp => hBd p (hDense hp),
    fun p hp q hq => hHH p (hDense hp) q (hDense hq)⟩

end Yau.LeafProofs.L05AutonomousAux
