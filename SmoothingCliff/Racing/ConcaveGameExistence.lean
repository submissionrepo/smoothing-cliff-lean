import Econlib.GameTheory.Equilibrium.Existence

/-!
# Nash existence for concave games

Proposition `prop:rentdissipation` (ii) in `Smoothing_the_Cliff_ITCS.tex` invokes
Debreu--Glicksberg--Fan existence for a game whose payoffs are strictly concave
in the own action.  Mathlib has no fixed-point theorem of the Brouwer or
Kakutani family, and Econlib's `NashExistenceData` requires the payoff to be
*affine* in the own strategy, which is the mixed-extension setting of Nash 1951
rather than a concave game on a real action set.

This file supplies the concave-game variant.  It follows Econlib's derivation
and reuses its Kakutani fixed-point theorem and its argmax machinery verbatim;
the single change is the convexity field.  Affineness is only ever used to make
the per-player argmax convex, and quasiconcavity does the same job, so the
structure below asks exactly for that and nothing else.  Since affine implies
concave implies quasiconcave, this is a strict generalization.
-/

namespace SmoothingCliff.Racing

open Econlib Econlib.GameTheory

universe u v

/-- Data for Kakutani-based existence in a **concave** game.  Identical to
Econlib's `NashExistenceData` except that the own-strategy requirement is
quasiconcavity of an ambient representative rather than affineness. -/
structure ConcaveNashExistenceData where
  /-- Player index. -/
  Player : Type u
  [instFintypePlayer : Fintype Player]
  [instInhabitedPlayer : Inhabited Player]
  [instDecEqPlayer : DecidableEq Player]
  /-- Per-player ambient strategy space. -/
  V : Player → Type v
  [instNAG : ∀ i, NormedAddCommGroup (V i)]
  [instNS : ∀ i, NormedSpace ℝ (V i)]
  [instFD : ∀ i, FiniteDimensional ℝ (V i)]
  /-- Per-player strategy slice. -/
  Slice : (i : Player) → Set (V i)
  hSlice_convex : ∀ i, Convex ℝ (Slice i)
  hSlice_compact : ∀ i, IsCompact (Slice i)
  hSlice_nonempty : ∀ i, (Slice i).Nonempty
  /-- Per-player payoff. -/
  payoff : (i : Player) → ((j : Player) → ↑(Slice j)) → ℝ
  payoff_continuous : ∀ i, Continuous (payoff i)
  /-- Quasiconcave in the own strategy: for every fixed background there is an
  ambient function, quasiconcave on the slice, agreeing with the payoff there.
  This is all that the convexity of the best-response set needs. -/
  payoff_quasiconcave_in_own : ∀ (i : Player) (σ : (j : Player) → ↑(Slice j)),
    ∃ g : V i → ℝ, QuasiconcaveOn ℝ (Slice i) g ∧
      ∀ y : ↑(Slice i), g y.1 = payoff i (Function.update σ i y)

attribute [instance] ConcaveNashExistenceData.instFintypePlayer
  ConcaveNashExistenceData.instInhabitedPlayer
  ConcaveNashExistenceData.instDecEqPlayer ConcaveNashExistenceData.instNAG
  ConcaveNashExistenceData.instNS ConcaveNashExistenceData.instFD

namespace ConcaveNashExistenceData

variable (D : ConcaveNashExistenceData)

/-- Profile space induced by the data. -/
abbrev Profile : Type _ := (i : D.Player) → ↑(D.Slice i)

/-- The equilibrium problem associated to the data. -/
def toEquilibriumProblem : EquilibriumProblem where
  S := D.Profile
  I := D.Player
  swap i σ σ' := ∃ y : ↑(D.Slice i), σ' = Function.update σ i y
  value := D.payoff

/-- Raw strategy set. -/
def mixedStrategySet : Set ((i : D.Player) → D.V i) :=
  Set.pi Set.univ D.Slice

/-- Bridge from a raw point of the strategy set to a subtype profile. -/
def liftToProfile {x : (i : D.Player) → D.V i} (hx : x ∈ D.mixedStrategySet) :
    D.Profile :=
  fun i => ⟨x i, hx i (Set.mem_univ i)⟩

lemma mixedStrategySet_convex : Convex ℝ D.mixedStrategySet :=
  convex_pi (fun i _ => D.hSlice_convex i)

lemma mixedStrategySet_compact : IsCompact D.mixedStrategySet :=
  isCompact_univ_pi fun i => D.hSlice_compact i

lemma mixedStrategySet_nonempty : D.mixedStrategySet.Nonempty := by
  refine ⟨fun i => (D.hSlice_nonempty i).choose, ?_⟩
  intro i _
  exact (D.hSlice_nonempty i).choose_spec

/-- Best-response correspondence at a raw background point. -/
def bestResponseSet (x : ↑D.mixedStrategySet) :
    Set ((i : D.Player) → D.V i) :=
  { y |
    ∃ hy : y ∈ D.mixedStrategySet,
      ∀ i (z : ↑(D.Slice i)),
        D.payoff i
            (Function.update (D.liftToProfile x.2) i
              ⟨y i, hy i (Set.mem_univ i)⟩) ≥
          D.payoff i (Function.update (D.liftToProfile x.2) i z) }

lemma bestResponseSet_subset (x : ↑D.mixedStrategySet) :
    D.bestResponseSet x ⊆ D.mixedStrategySet :=
  fun _ hy => hy.1

/-- Player `i`'s payoff from deviating to a slice element against a fixed
background. -/
def slicePayoff (i : D.Player) (x : ↑D.mixedStrategySet) (z : ↑(D.Slice i)) :
    ℝ :=
  D.payoff i (Function.update (D.liftToProfile x.2) i z)

lemma update_continuous (i : D.Player) :
    Continuous fun q : D.Profile × ↑(D.Slice i) => Function.update q.1 i q.2 := by
  apply continuous_pi
  intro j
  by_cases hj : j = i
  · have hrw : (fun q : D.Profile × ↑(D.Slice i) =>
        Function.update q.1 i q.2 j) = fun q => hj ▸ q.2 := by
      funext q
      subst hj
      rw [Function.update_self]
    rw [hrw]
    cases hj
    exact continuous_snd
  · have hrw : (fun q : D.Profile × ↑(D.Slice i) =>
        Function.update q.1 i q.2 j) = fun q => q.1 j := by
      funext q
      rw [Function.update_of_ne hj]
    rw [hrw]
    exact (continuous_apply j).comp continuous_fst

lemma slicePayoff_continuous (i : D.Player) :
    Continuous fun p : ↑D.mixedStrategySet × ↑(D.Slice i) =>
      D.slicePayoff i p.1 p.2 := by
  have h_lift : Continuous fun p : ↑D.mixedStrategySet × ↑(D.Slice i) =>
      D.liftToProfile p.1.2 :=
    continuous_pi fun j => Continuous.subtype_mk
      ((continuous_apply j).comp (continuous_subtype_val.comp continuous_fst)) _
  exact (D.payoff_continuous i).comp
    ((D.update_continuous i).comp (h_lift.prodMk continuous_snd))

lemma bestResponseSet_eq (x : ↑D.mixedStrategySet) :
    D.bestResponseSet x = Set.univ.pi fun i =>
      Subtype.val '' Optimization.argmax (D.slicePayoff i x) Set.univ := by
  ext y
  simp only [Set.mem_univ_pi]
  constructor
  · rintro ⟨hy, hopt⟩ i
    exact ⟨⟨y i, hy i (Set.mem_univ i)⟩, ⟨Set.mem_univ _, fun z _ => hopt i z⟩,
      rfl⟩
  · intro h
    have hy : y ∈ D.mixedStrategySet := by
      intro i _
      obtain ⟨w, -, hw⟩ := h i
      exact hw ▸ w.2
    refine ⟨hy, fun i z => ?_⟩
    obtain ⟨w, ⟨-, hw_max⟩, hw⟩ := h i
    have h_wi : (⟨y i, hy i (Set.mem_univ i)⟩ : ↑(D.Slice i)) = w :=
      Subtype.ext hw.symm
    rw [h_wi]
    exact hw_max (Set.mem_univ z)

lemma bestResponseSet_nonempty (x : ↑D.mixedStrategySet) :
    (D.bestResponseSet x).Nonempty := by
  rw [bestResponseSet_eq, Set.univ_pi_nonempty_iff]
  intro i
  haveI : CompactSpace ↑(D.Slice i) :=
    isCompact_iff_compactSpace.mp (D.hSlice_compact i)
  haveI : Nonempty ↑(D.Slice i) := (D.hSlice_nonempty i).to_subtype
  have h_cont : Continuous (D.slicePayoff i x) :=
    (D.slicePayoff_continuous i).comp (continuous_const.prodMk continuous_id)
  exact (Optimization.argmax_nonempty isCompact_univ Set.univ_nonempty
    h_cont.continuousOn).image _

/-- **The one changed step.**  Quasiconcavity of an ambient representative is
what makes the per-player argmax convex; Econlib derives the same fact from
affineness. -/
lemma bestResponseSet_convex (x : ↑D.mixedStrategySet) :
    Convex ℝ (D.bestResponseSet x) := by
  rw [bestResponseSet_eq]
  refine convex_pi fun i _ => ?_
  obtain ⟨g, hg_quasi, hg_match⟩ :=
    D.payoff_quasiconcave_in_own i (D.liftToProfile x.2)
  have h_match : ∀ z : ↑(D.Slice i), D.slicePayoff i x z = g z.1 :=
    fun z => (hg_match z).symm
  rw [Optimization.image_val_argmax_univ h_match]
  exact Optimization.argmax_convex hg_quasi

lemma bestResponseSet_closedGraph :
    IsClosedGraph (fun x : ↑D.mixedStrategySet => D.bestResponseSet x) := by
  have h_player (i : D.Player) : IsClosed { w : ↑D.mixedStrategySet × D.V i |
      w.2 ∈ Subtype.val '' Optimization.argmax (D.slicePayoff i w.1)
        Set.univ } := by
    haveI : CompactSpace ↑(D.Slice i) :=
      isCompact_iff_compactSpace.mp (D.hSlice_compact i)
    haveI : Nonempty ↑(D.Slice i) := (D.hSlice_nonempty i).to_subtype
    have hf_cont := D.slicePayoff_continuous i
    have h_uhc := Optimization.argmax_upperHemicontinuous hf_cont .const .const
      (fun _ => isCompact_univ) fun _ => Set.univ_nonempty
    exact (h_uhc.isClosedGraph fun x =>
      (Optimization.argmax_isCompact (f := D.slicePayoff i) hf_cont
        (fun _ => isCompact_univ) x).isClosed).image_subtypeVal
      (D.hSlice_compact i).isClosed
  have h_graph_eq : { z : ↑D.mixedStrategySet × ((j : D.Player) → D.V j) |
        z.2 ∈ D.bestResponseSet z.1 } =
      ⋂ i, (fun z : ↑D.mixedStrategySet × ((j : D.Player) → D.V j) =>
          (z.1, z.2 i)) ⁻¹'
        { w : ↑D.mixedStrategySet × D.V i |
          w.2 ∈ Subtype.val '' Optimization.argmax (D.slicePayoff i w.1)
            Set.univ } := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage,
      bestResponseSet_eq, Set.mem_univ_pi]
  rw [IsClosedGraph, h_graph_eq]
  exact isClosed_iInter fun i => (h_player i).preimage
    (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd))

/-- **Debreu--Glicksberg--Fan existence.**  A concave game with compact convex
slices, continuous payoffs and own-strategy quasiconcavity has a pure-strategy
equilibrium.  This is the hypothesis `prop:rentdissipation` (ii) invokes. -/
theorem exists_equilibrium :
    ∃ σ : D.Profile, D.toEquilibriumProblem.IsEquilibrium σ := by
  letI : NormedAddCommGroup ((i : D.Player) → D.V i) := Pi.normedAddCommGroup
  letI : NormedSpace ℝ ((i : D.Player) → D.V i) := Pi.normedSpace
  letI : FiniteDimensional ℝ ((i : D.Player) → D.V i) :=
    FiniteDimensional.finiteDimensional_pi' ℝ D.V
  obtain ⟨⟨xstar, hxstar⟩, h_fixed⟩ := kakutaniFixedPoint
    D.mixedStrategySet D.mixedStrategySet_convex D.mixedStrategySet_compact
    D.mixedStrategySet_nonempty
    (fun x => D.bestResponseSet x) D.bestResponseSet_closedGraph
    (fun x => ⟨D.bestResponseSet_subset x, D.bestResponseSet_convex x,
      D.bestResponseSet_nonempty x⟩)
  obtain ⟨h_mem, h_opt⟩ := h_fixed
  refine ⟨D.liftToProfile h_mem, ?_⟩
  intro i σ' hswap
  obtain ⟨y, hy⟩ := hswap
  subst hy
  have hopt_i := h_opt i y
  have h_lhs : Function.update (D.liftToProfile hxstar) i
      ⟨xstar i, h_mem i (Set.mem_univ i)⟩ = D.liftToProfile hxstar :=
    Function.update_eq_self (β := fun i => ↑(D.Slice i)) i _
  rw [h_lhs] at hopt_i
  exact hopt_i

end ConcaveNashExistenceData

end SmoothingCliff.Racing
